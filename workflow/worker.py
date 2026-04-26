import os
import sys
from pathlib import Path
from redis import Redis
import rq

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.runner import run_single_spec

listen = ['high', 'default', 'low']

redis_conn = Redis.from_url(os.getenv('REDIS_URL', 'redis://localhost:6379'))

if __name__ == '__main__':
    with rq.Connection(redis_conn):
        worker = rq.Worker(map(rq.Queue, listen))
        worker.work()
