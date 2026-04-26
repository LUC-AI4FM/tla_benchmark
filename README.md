# TLA+ Benchmark

This repository contains the tools to run benchmarks for TLA+ specifications using different models.

## Experiment Execution Workflow

The experiment execution is managed through a distributed job queue system. This allows for running multiple experiments in parallel across different machines, including those with GPUs.

The architecture consists of three main components:
1.  **Web UI (Streamlit)**: A web-based dashboard to configure and submit new experiment jobs.
2.  **Job Queue (Redis & RQ)**: A Redis server acts as a message broker for the Python RQ (Redis Queue) library. The UI adds jobs to the queue.
3.  **Workers (RQ)**: Python scripts running on one or more server machines that listen for jobs on the queue, execute them, and report results.

## Setup and Installation

1.  **Clone the repository**:
    ```bash
    git clone <repository-url>
    cd tla_benchmark
    ```

2.  **Install dependencies**:
    Ensure you have Python 3.9+ installed. It is recommended to use a virtual environment.
    ```bash
    pip install -r requirements.txt
    ```

3.  **Redis Server**:
    You need a Redis server running and accessible from the machine running the Web UI and all worker machines. You can run Redis using Docker or install it directly.
    ```bash
    # Example using Docker
    docker run -d -p 6379:6379 redis
    ```

4.  **Weights & Biases (wandb)**:
    This project uses Weights & Biases for experiment tracking. You need to be logged into your `wandb` account.
    ```bash
    wandb login
    ```

## Running the Workflow

Follow these steps to start the system.

**Step 1: Start the RQ Dashboard (Optional)**

The RQ Dashboard provides a web interface to monitor the status of your queues and jobs.
```bash
rq-dashboard
```
You can access it at `http://localhost:9181`.

**Step 2: Start the RQ Workers**

On each machine that will execute the experiments (e.g., the GPU servers), run the worker script. Make sure to activate the correct Python environment first.

Open a terminal on each server and run:
```bash
# Example for a server
# cd /path/to/tla_benchmark
# conda activate your_env
python workflow/worker.py
```
The worker will connect to the Redis server and wait for jobs.

**Step 3: Start the Streamlit Web UI**

On your local machine (or a server), start the Streamlit dashboard.
```bash
streamlit run workflow/dashboard.py
```
This will open a new tab in your browser with the UI.

**Step 4: Submit an Experiment**

1.  Open the Streamlit UI in your browser.
2.  Select the desired model and specification file.
3.  Choose the target machine and GPU for the experiment.
4.  Enter the required API key (e.g., for OpenAI).
5.  Click "Run Experiment".

The job will be sent to the Redis queue, and one of the available workers will pick it up and start the execution. You can monitor the job's progress in the RQ Dashboard and see the terminal output of the worker.

