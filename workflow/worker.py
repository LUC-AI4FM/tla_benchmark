import os
import sys
import argparse
import socket
from pathlib import Path
from redis import Redis
import rq

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.runner import run_single_spec

redis_conn = Redis.from_url(os.getenv('REDIS_URL', 'redis://localhost:6379'))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="RQ Worker for TLA+ Bench Eval")
    parser.add_argument('queues', nargs='*', help="Queues to listen to")
    args = parser.parse_args()
    
    if args.queues:
        listen = args.queues
    else:
        hostname = socket.gethostname()
        listen = [hostname, 'default', 'local']

    print(f"Worker listening on queues: {listen}")
    queues = [rq.Queue(name, connection=redis_conn) for name in listen]
    worker = rq.Worker(queues, connection=redis_conn)
    worker.work()
