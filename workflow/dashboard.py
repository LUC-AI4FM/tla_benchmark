import streamlit as st
import os
import sys
from pathlib import Path
from redis import Redis
from rq import Queue, job
from rq.exceptions import NoSuchJobError
import time
import itertools

sys.path.insert(0, str(Path(__file__).parent.parent))
from src.utils import load_json

st.set_page_config(layout="wide")
st.title("TLA+ Benchmark Distributed Runner")

@st.cache_data
def load_all_configs():
    models_cfg = load_json("configs/models.json")
    models = {model['id']: model for model in models_cfg}
    
    prompt_dir = Path("configs/prompts")
    prompts = [f.stem for f in prompt_dir.glob("*.txt")]
    
    spec_versions = {}
    data_dir = Path("data")
    for version_dir in data_dir.iterdir():
        if version_dir.is_dir() and version_dir.name.endswith("_json"):
            version_name = version_dir.name.replace("_json", "")
            spec_ids = sorted([int(f.stem) for f in version_dir.glob("*.json")])
            spec_versions[version_name] = spec_ids
            
    return models, prompts, spec_versions

models, prompts, spec_versions = load_all_configs()

redis_url = os.getenv('REDIS_URL', 'redis://localhost:6379')
redis_conn = Redis.from_url(redis_url)

if 'jobs' not in st.session_state:
    st.session_state.jobs = {}

st.sidebar.header("Cluster Configuration")
machines = {
    "local": {"gpus": [0]},
    "aisec-101.cs.luc.edu": {"gpus": [0, 1, 2]},
    "aisec-102.cs.luc.edu": {"gpus": [0, 1]},
}
selected_machine = st.sidebar.selectbox("Target Machine", list(machines.keys()))

if selected_machine != "local":
    st.sidebar.info(
        f"**Note:** To run jobs on {selected_machine}, start the worker directly on that machine pointing to your central Redis server:\n"
        f"`python workflow/worker.py {selected_machine}`\n\n"
        "Secure the Redis connection via the `REDIS_URL` environment variable."
    )

selected_gpus = st.sidebar.multiselect(
    "Target GPU IDs", 
    machines[selected_machine]["gpus"], 
    default=machines[selected_machine]["gpus"]
)

st.sidebar.header("API Configuration")
user_api_key = st.sidebar.text_input("OpenAI API Key (if needed)", type="password")

st.header("Experiment Configuration")

col1, col2 = st.columns(2)
with col1:
    selected_prompt = st.selectbox("Select a Prompt", prompts)
    
    st.write("**Models**")
    c1, c2 = st.columns(2)
    with c1:
        if st.button("Select All Models", use_container_width=True):
            st.session_state.models_selection = list(models.keys())
    with c2:
        if st.button("Clear Models", use_container_width=True):
            st.session_state.models_selection = []
            
    selected_models = st.multiselect("Select Models", list(models.keys()), key="models_selection")

with col2:
    selected_version = st.selectbox("Select Specification Version", list(spec_versions.keys()))
    available_specs = spec_versions.get(selected_version, [])
    
    st.write("**Specifications**")
    c3, c4 = st.columns(2)
    with c3:
        if st.button("Select All Specs", use_container_width=True):
            st.session_state.specs_selection = available_specs
    with c4:
        if st.button("Clear Specs", use_container_width=True):
            st.session_state.specs_selection = []
            
    selected_specs = st.multiselect("Select Specification IDs", available_specs, key="specs_selection")

st.header("Run Experiment Batch")
condition = "zero-shot"

if st.button("Queue Experiments"):
    if not selected_models or not selected_specs:
        st.error("Please select at least one model and one specification ID.")
    elif not selected_gpus:
        st.error("Please select at least one GPU for execution.")
    else:
        total_jobs = len(selected_models) * len(selected_specs)
        st.info(f"Queuing {total_jobs} jobs...")
        progress_bar = st.progress(0)
        
        queued_count = 0
        gpu_cycle = itertools.cycle(selected_gpus)
        
        for model_name in selected_models:
            for spec_id in selected_specs:
                model_cfg = models[model_name]
                
                if model_cfg.get("backend") == "openai" and not user_api_key:
                    st.error(f"Model '{model_name}' requires an OpenAI API key. Please provide it in the sidebar.")
                    continue

                q = Queue(name=selected_machine, connection=redis_conn)
                assigned_gpu = next(gpu_cycle)
                
                job_kwargs = {
                    'spec_id': str(spec_id),
                    'spec_version': selected_version,
                    'model_cfg': model_cfg,
                    'prompt_name': selected_prompt,
                    'condition': condition,
                    'api_key': user_api_key,
                    'gpu_id': assigned_gpu
                }
                
                new_job = q.enqueue(
                    'src.runner.run_single_spec',
                    kwargs=job_kwargs,
                    job_timeout=3600,
                    result_ttl=86400
                )
                st.session_state.jobs[new_job.id] = {
                    "model": model_name,
                    "spec_id": spec_id,
                    "version": selected_version,
                    "gpu_id": assigned_gpu
                }
                queued_count += 1
                progress_bar.progress(queued_count / total_jobs)

        st.success(f"Successfully queued {queued_count} jobs on machine '{selected_machine}'.")
        time.sleep(1)
        st.rerun()

st.header("Queued Jobs")

if not st.session_state.jobs:
    st.info("No jobs have been queued in this session.")
else:
    headers = ["Job ID", "Model", "Spec ID", "Version", "GPU", "Status", "Action"]
    
    rows = []
    jobs_to_remove_on_clear = []

    for job_id, job_info in list(st.session_state.jobs.items()):
        try:
            j = job.Job.fetch(job_id, connection=redis_conn)
            status_enum = j.get_status()
            status = status_enum.value if hasattr(status_enum, 'value') else str(status_enum)
            
            row_data = {
                "Job ID_Short": job_id[:8],
                "Job ID_Full": job_id,
                "Model": job_info['model'],
                "Spec ID": job_info['spec_id'],
                "Version": job_info['version'],
                "GPU": str(job_info.get('gpu_id', 'N/A')),
                "Status": status,
                "Action": status
            }
            rows.append(row_data)

        except Exception:
            jobs_to_remove_on_clear.append(job_id)

    cols = st.columns(len(headers))
    for col, header in zip(cols, headers):
        col.write(f"**{header}**")

    for row in rows:
        cols = st.columns(len(headers))
        cols[0].text(row["Job ID_Short"])
        cols[1].text(row["Model"])
        cols[2].text(row["Spec ID"])
        cols[3].text(row["Version"])
        cols[4].text(row["GPU"])
        cols[5].text(row["Status"])
        
        action_status = row["Action"]
        action_col = cols[6]

        if action_status in ['queued', 'scheduled', 'started', 'deferred']:
            if action_col.button("Stop", key=f"stop_{row['Job ID_Full']}"):
                try:
                    j = job.Job.fetch(row['Job ID_Full'], connection=redis_conn)
                    j.cancel()
                    st.toast(f"Job {row['Job ID_Short']} cancelled.")
                except NoSuchJobError:
                    st.toast(f"Job {row['Job ID_Short']} no longer exists.")
                    jobs_to_remove_on_clear.append(row['Job ID_Full'])
                except Exception as e:
                    st.error(f"Failed to cancel: {e}")
                st.rerun()
                
        elif action_status in ['finished', 'failed', 'canceled', 'stopped']:
            if action_col.button("Clear", key=f"clear_{row['Job ID_Full']}"):
                jobs_to_remove_on_clear.append(row['Job ID_Full'])
                st.rerun()

    if jobs_to_remove_on_clear:
        for job_id in jobs_to_remove_on_clear:
            if job_id in st.session_state.jobs:
                del st.session_state.jobs[job_id]
        st.rerun()

    time.sleep(5)
    st.rerun()