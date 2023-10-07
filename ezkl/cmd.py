import os, subprocess

os.system("ezkl table -M network.onnx")
os.system('ezkl gen-settings -M network.onnx')
os.system('ezkl get-srs -S settings.json')
os.system('ezkl compile-circuit -M network.onnx -S settings.json --compiled-circuit network.ezkl')
os.system('ezkl setup -M network.ezkl --srs-path=kzg.srs --vk-path=vk.key --pk-path=pk.key')
os.system('ezkl gen-witness -D input.json -M network.ezkl')
os.system('ezkl prove -M network.ezkl --witness witness.json --pk-path=pk.key --proof-path=model.proof --srs-path=kzg.srs')
os.system('ezkl verify --proof-path=model.proof --settings-path=settings.json --vk-path=vk.key --srs-path=kzg.srs')
