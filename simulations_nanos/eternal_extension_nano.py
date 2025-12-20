cat > simulations_nanos/eternal_extension_nano.py <<EOF
from eternal_extension_module import EternalExtensionModule

extension = EternalExtensionModule()

demo = "result = 42"

print(extension.extend_with_framework("math", demo))
EOF

