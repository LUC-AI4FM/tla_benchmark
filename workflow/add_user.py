#!/usr/bin/env python3
import sys
import getpass
from pathlib import Path

import bcrypt
import yaml

USERS_YAML = Path(__file__).parent / "users.yaml"


def main():
    if len(sys.argv) < 2:
        print("Usage: python workflow/add_user.py <username>")
        sys.exit(1)

    uname = sys.argv[1]

    with open(USERS_YAML) as f:
        config = yaml.load(f, Loader=yaml.SafeLoader)

    existing = config["credentials"]["usernames"].get(uname, {})
    email = input(f"Email [{existing.get('email', '')}]: ").strip() or existing.get("email", "")
    display_name = input(f"Display name [{existing.get('name', uname)}]: ").strip() or existing.get("name", uname)
    make_admin = input("Admin? [y/N]: ").strip().lower() == "y"
    password = getpass.getpass(f"Password for {uname}: ")
    confirm = getpass.getpass("Confirm password: ")

    if password != confirm:
        print("Passwords do not match.")
        sys.exit(1)

    hashed = bcrypt.hashpw(password.encode(), bcrypt.gensalt()).decode()

    config["credentials"]["usernames"][uname] = {
        "email": email,
        "name": display_name,
        "password": hashed,
        "admin": make_admin,
    }

    with open(USERS_YAML, "w") as f:
        yaml.dump(config, f, default_flow_style=False, allow_unicode=True)

    print(f"User '{uname}' ({display_name}) saved.")


if __name__ == "__main__":
    main()
