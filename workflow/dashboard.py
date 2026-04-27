import streamlit as st
import os
import sys
import json
from pathlib import Path
import yaml
from redis import Redis
from rq import Queue, job
from rq.exceptions import NoSuchJobError
import time
import itertools
import streamlit_authenticator as stauth

sys.path.insert(0, str(Path(__file__).parent.parent))
from src.utils import load_json

st.set_page_config(layout="wide", page_title="TLA+ Benchmark Runner")

_USERS_YAML = Path(__file__).parent / "users.yaml"
with open(_USERS_YAML) as f:
    _auth_config = yaml.load(f, Loader=yaml.SafeLoader)

authenticator = stauth.Authenticate(
    _auth_config["credentials"],
    _auth_config["cookie"]["name"],
    _auth_config["cookie"]["key"],
    _auth_config["cookie"]["expiry_days"],
)

try:
    authenticator.login()
except Exception as e:
    st.error(str(e))

_auth = st.session_state.get("authentication_status")
if _auth is False:
    st.error("Incorrect username or password.")
    st.stop()
elif _auth is None:
    st.title("TLA+ Benchmark Distributed Runner")
    st.info("Please log in to continue.")
    st.stop()

username: str = st.session_state["username"]
name: str = st.session_state["name"]
is_admin: bool = _auth_config["credentials"]["usernames"].get(username, {}).get("admin", False)

redis_url = os.getenv("REDIS_URL", "redis://localhost:6379")
redis_conn = Redis.from_url(redis_url)

_JOBS_KEY = f"dashboard:jobs:{username}"


def _load_jobs() -> dict:
    raw = redis_conn.get(_JOBS_KEY)
    return json.loads(raw) if raw else {}


def _save_jobs(jobs: dict):
    redis_conn.set(_JOBS_KEY, json.dumps(jobs))


if "jobs_loaded" not in st.session_state:
    st.session_state.jobs = _load_jobs()
    st.session_state.jobs_loaded = True


@st.cache_data
def load_all_configs():
    models_cfg = load_json("configs/models.json")
    models = {model["id"]: model for model in models_cfg}

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

st.sidebar.write(f"Logged in as **{name}**")
authenticator.logout("Logout", "sidebar")

st.sidebar.header("Cluster Configuration")
machines = {
    "local": {"gpus": [0]},
    "aisec-101.cs.luc.edu": {"gpus": [0, 1, 2]},
    "aisec-102.cs.luc.edu": {"gpus": [0, 1]},
    "plantain.cs.luc.edu": {"gpus": [0, 1, 2, 3, 4, 5, 6, 7]},
}
selected_machine = st.sidebar.selectbox("Target Machine", list(machines.keys()))

if selected_machine != "local":
    st.sidebar.info(
        f"Start the worker on {selected_machine}:\n"
        f"`python workflow/worker.py {selected_machine}`"
    )

selected_gpus = st.sidebar.multiselect(
    "Target GPU IDs",
    machines[selected_machine]["gpus"],
    default=machines[selected_machine]["gpus"],
)

st.sidebar.header("API Keys")
user_api_key = st.sidebar.text_input("OpenAI API Key (if needed)", type="password")

st.sidebar.header("Weights & Biases")
wandb_project = st.sidebar.text_input("W&B Project", value="tla_bench")
wandb_entity = st.sidebar.text_input("W&B Entity / Team", value="ai4fm")
wandb_api_key = st.sidebar.text_input("W&B API Key", type="password")

st.title("TLA+ Benchmark Distributed Runner")
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
        missing_key_models = [
            m for m in selected_models
            if models[m].get("backend") == "openai" and not user_api_key
        ]
        if missing_key_models:
            for m in missing_key_models:
                st.error(f"Model '{m}' requires an OpenAI API key. Please provide it in the sidebar.")
        else:
            total_jobs = len(selected_models) * len(selected_specs)
            st.info(f"Queuing {total_jobs} jobs...")
            progress_bar = st.progress(0)

            queued_count = 0
            gpu_cycle = itertools.cycle(selected_gpus)

            for model_name in selected_models:
                for spec_id in selected_specs:
                    model_cfg = models[model_name]
                    q = Queue(name=selected_machine, connection=redis_conn)
                    assigned_gpu = next(gpu_cycle)

                    job_kwargs = {
                        "spec_id": str(spec_id),
                        "spec_version": selected_version,
                        "model_cfg": model_cfg,
                        "prompt_name": selected_prompt,
                        "condition": condition,
                        "api_key": user_api_key,
                        "gpu_id": assigned_gpu,
                        "wandb_project": wandb_project,
                        "wandb_entity": wandb_entity,
                        "wandb_api_key": wandb_api_key,
                    }

                    new_job = q.enqueue(
                        "src.runner.run_single_spec",
                        kwargs=job_kwargs,
                        job_timeout=3600,
                        result_ttl=86400,
                    )
                    st.session_state.jobs[new_job.id] = {
                        "model": model_name,
                        "spec_id": spec_id,
                        "version": selected_version,
                        "gpu_id": assigned_gpu,
                    }
                    queued_count += 1
                    progress_bar.progress(queued_count / total_jobs)

            _save_jobs(st.session_state.jobs)
            st.success(f"Successfully queued {queued_count} jobs on machine '{selected_machine}'.")
            time.sleep(1)
            st.rerun()

st.header("Queued Jobs")

if not st.session_state.jobs:
    st.info("No jobs have been queued in this session.")
else:
    headers = ["Job ID", "Model", "Spec ID", "Version", "GPU", "Status", "Action"]

    rows = []
    jobs_to_remove = []

    for job_id, job_info in list(st.session_state.jobs.items()):
        try:
            j = job.Job.fetch(job_id, connection=redis_conn)
            status_enum = j.get_status()
            status = status_enum.value if hasattr(status_enum, "value") else str(status_enum)
            rows.append({
                "Job ID_Short": job_id[:8],
                "Job ID_Full": job_id,
                "Model": job_info["model"],
                "Spec ID": job_info["spec_id"],
                "Version": job_info["version"],
                "GPU": str(job_info.get("gpu_id", "N/A")),
                "Status": status,
                "Action": status,
            })
        except Exception:
            jobs_to_remove.append(job_id)

    header_cols = st.columns(len(headers))
    for col, header in zip(header_cols, headers):
        col.write(f"**{header}**")

    for row in rows:
        cols = st.columns(len(headers))
        cols[0].text(row["Job ID_Short"])
        cols[1].text(row["Model"])
        cols[2].text(row["Spec ID"])
        cols[3].text(row["Version"])
        cols[4].text(row["GPU"])
        cols[5].text(row["Status"])

        if row["Action"] in ("queued", "scheduled", "started", "deferred"):
            if cols[6].button("Stop", key=f"stop_{row['Job ID_Full']}"):
                try:
                    j = job.Job.fetch(row["Job ID_Full"], connection=redis_conn)
                    j.cancel()
                    st.toast(f"Job {row['Job ID_Short']} cancelled.")
                except NoSuchJobError:
                    jobs_to_remove.append(row["Job ID_Full"])
                except Exception as e:
                    st.error(f"Failed to cancel: {e}")
                st.rerun()
        elif row["Action"] in ("finished", "failed", "canceled", "stopped"):
            if cols[6].button("Clear", key=f"clear_{row['Job ID_Full']}"):
                jobs_to_remove.append(row["Job ID_Full"])
                st.rerun()

    if jobs_to_remove:
        for job_id in jobs_to_remove:
            st.session_state.jobs.pop(job_id, None)
        _save_jobs(st.session_state.jobs)
        st.rerun()

    time.sleep(5)
    st.rerun()

if is_admin:
    st.header("Admin: All Users")
    all_keys = [k.decode() if isinstance(k, bytes) else k for k in redis_conn.scan_iter("dashboard:jobs:*")]
    for key in sorted(all_keys):
        user_slug = key.replace("dashboard:jobs:", "")
        raw = redis_conn.get(key)
        user_jobs = json.loads(raw) if raw else {}
        with st.expander(f"{user_slug}  ({len(user_jobs)} jobs)"):
            if not user_jobs:
                st.write("No jobs.")
                continue
            sub_headers = ["Job ID", "Model", "Spec ID", "Version", "GPU", "Status"]
            sub_cols = st.columns(len(sub_headers))
            for col, h in zip(sub_cols, sub_headers):
                col.write(f"**{h}**")
            for jid, jinfo in user_jobs.items():
                try:
                    j = job.Job.fetch(jid, connection=redis_conn)
                    status_enum = j.get_status()
                    status = status_enum.value if hasattr(status_enum, "value") else str(status_enum)
                except Exception:
                    status = "expired"
                row_cols = st.columns(len(sub_headers))
                row_cols[0].text(jid[:8])
                row_cols[1].text(jinfo.get("model", ""))
                row_cols[2].text(str(jinfo.get("spec_id", "")))
                row_cols[3].text(jinfo.get("version", ""))
                row_cols[4].text(str(jinfo.get("gpu_id", "N/A")))
                row_cols[5].text(status)
