import streamlit as st
import os
import sys
from pathlib import Path
from redis import Redis
from rq import Queue

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.utils import load_json

st.set_page_config(layout="wide")

st.title("TLA+ Benchmark Distributed Runner")


redis_conn = Redis.from_url(os.getenv('REDIS_URL', 'redis://localhost:6379'))


st.sidebar.header("API Configuration")
st.sidebar.info(
    "To run experiments, please provide your OpenAI API key. "
    "Your key will not be stored."
)
user_api_key = st.sidebar.text_input("OpenAI API Key", type="password")

if not user_api_key:
    st.warning("Please enter your OpenAI API key in the sidebar to begin.")
    st.stop()


st.sidebar.header("Cluster Configuration")
machines = {
    "aisec-101.cs.luc.edu": {"gpus": [0, 1, 2]},
    "aisec-102.cs.luc.edu": {"gpus": [0, 1]},
}
selected_machine = st.sidebar.selectbox("Target Machine", list(machines.keys()))
selected_gpu = st.sidebar.selectbox("Target GPU ID", machines[selected_machine]["gpus"])



@st.cache_data
def load_configs():
    models_cfg = load_json("configs/models.json")
    online_models = {k: v for k, v in models_cfg.items() if v.get("backend") == "openai"}
    test_split = load_json("data/test_split.json")
    spec_ids = test_split.get("test", [])
    return online_models, spec_ids

models, spec_ids = load_configs()
model_names = list(models.keys())



st.header("Run a Single Experiment")

col1, col2 = st.columns(2)
with col1:
    selected_model_name = st.selectbox("Select a Model", model_names)
with col2:
    selected_spec_id = st.selectbox("Select a Specification ID", spec_ids)

prompt_name = "nlp_to_tla"
condition = "zero-shot"

run_button = st.button("Queue Experiment")

if run_button:
    if not selected_model_name or not selected_spec_id:
        st.error("Please select a model and a specification ID.")
    else:
        model_cfg = models[selected_model_name]
        
        q = Queue(name=selected_machine, connection=redis_conn)
        
        job_kwargs = {
            'spec_id': selected_spec_id,
            'model_cfg': model_cfg,
            'prompt_name': prompt_name,
            'condition': condition,
            'api_key': user_api_key,
            'gpu_id': selected_gpu
        }
        
        q.enqueue(
            'src.runner.run_single_spec',
            kwargs=job_kwargs,
            job_timeout=3600,
            result_ttl=86400
        )
        
        st.success(f"Successfully queued job for spec **{selected_spec_id}** on **{selected_machine}** (GPU: {selected_gpu}).")
        st.info("Monitor job status in the RQ Dashboard.")
