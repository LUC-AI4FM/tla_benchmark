#!/usr/bin/env bash
set -e

echo "==> Installing Python dependencies"
pip3 install -r requirements.txt

echo "==> Setting cookie secret"
if grep -q "REPLACE_WITH_RANDOM_SECRET_KEY" workflow/users.yaml; then
    SECRET=$(python3 -c "import secrets; print(secrets.token_hex(32))")
    sed -i "s/REPLACE_WITH_RANDOM_SECRET_KEY/$SECRET/" workflow/users.yaml
    echo "    Secret set."
else
    echo "    Already set, skipping."
fi

echo "==> Setting your dashboard password"
python3 workflow/add_user.py arslanbisharat

echo "==> Starting Redis"
sudo systemctl enable --now redis-server

echo "==> Installing dashboard systemd service"
sudo cp workflow/tla-dashboard.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now tla-dashboard
echo "    Status: $(sudo systemctl is-active tla-dashboard)"

echo "==> Installing nginx"
sudo apt-get install -y nginx certbot python3-certbot-nginx

echo "==> Configuring nginx"
sudo cp workflow/nginx.conf /etc/nginx/sites-available/tla-dashboard
sudo ln -sf /etc/nginx/sites-available/tla-dashboard /etc/nginx/sites-enabled/tla-dashboard
sudo nginx -t
sudo systemctl reload nginx

echo "==> Obtaining SSL certificate for ai4fm.cs.luc.edu"
echo "    (requires ai4fm.cs.luc.edu DNS to point to this machine)"
sudo certbot --nginx -d ai4fm.cs.luc.edu

echo ""
echo "Done. Dashboard is live at https://ai4fm.cs.luc.edu"
