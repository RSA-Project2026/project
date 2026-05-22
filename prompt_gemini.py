import os
from google import genai
from dotenv import load_dotenv

# Step 0: Setup Gemini API client and get source code of protocol implementation
load_dotenv()
client = genai.Client(api_key=os.getenv("GEMINI_API_KEY"))

selected_implementation = "essential"
with open(f"implementations/{selected_implementation}.py", "r", encoding="utf-8") as f:
    source_code = f.read()

temperature = 0.1

# Step 1: Generate a draft analysis of the source code, identifying key components and their interactions. This will help in understanding the protocol's structure and behavior, which is crucial for writing an accurate TLA+ specification.
with open("prompts/thinking_prompt.txt", "r", encoding="utf-8") as f:
    thinking_prompt = f.read().format(source_code=source_code)

draft_analysis = client.models.generate_content(
    model="gemini-3.5-flash",
    contents=thinking_prompt,
    temperature=temperature
)
draft_analysis = draft_analysis.text

print("STEP 1 OUTPUT:\n", draft_analysis)

# Step 2: Write a TLA+ specification based on the draft analysis. The specification should capture the essential properties and behaviors of the protocol, including its states, transitions, and invariants.
with open("prompts/writing_prompt.txt", "r", encoding="utf-8") as f:
    writing_prompt = f.read().format(source_code=source_code, draft_analysis=draft_analysis)

generated_specification = client.models.generate_content(
    model="gemini-3.5-flash",
    contents=writing_prompt,
    temperature=temperature
)
generated_specification = generated_specification.text

with open(f"outputs/{selected_implementation}/generated_specification.tla", "w", encoding="utf-8") as f:
    f.write(generated_specification)
print("STEP 2 OUTPUT:\n", generated_specification)

# Step 3: Generate a configuration file for the TLA+ model checker (e.g., TLC) based on the generated TLA+ specification. The configuration file should specify the parameters for model checking, such as the properties to be verified and the state space to be explored.
with open("prompts/cfg_prompt.txt", "r", encoding="utf-8") as f:
    cfg_prompt = f.read().format(tla_spec=generated_specification)

generated_cfg = client.models.generate_content(
    model="gemini-3.5-flash",
    contents=cfg_prompt,
    temperature=temperature
)
generated_cfg = generated_cfg.text

with open(f"outputs/{selected_implementation}/generated_cfg.cfg", "w", encoding="utf-8") as f:
    f.write(generated_cfg)
print("STEP 3 OUTPUT:\n", generated_cfg)
