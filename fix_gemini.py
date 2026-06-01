import json
import os
from google import genai
from dotenv import load_dotenv

# Step 0: Setup Gemini API client and various variables.
load_dotenv()
client = genai.Client(api_key=os.getenv("GEMINI_API_KEY"))
selected_implementation = "functional"

# Step 1: Read the generated TLA+ specification and configuration file for the selected implementation. This will serve as the basis for identifying any issues or inconsistencies that need to be addressed in the fixing process.
with open(f"generated_specs/paxos_{selected_implementation}/direct_call/paxos_{selected_implementation}.tla", "r", encoding="utf-8") as f:
    tla_code = f.read()

with open(f"generated_specs/paxos_{selected_implementation}/direct_call/paxos_{selected_implementation}.cfg", "r", encoding="utf-8") as f:
    cfg_code = f.read()

# Step 2: Retrieve the results of the compilation and runtime checks for the latest generated specification. This information will be crucial for understanding the specific issues that need to be addressed in the fixing process.
output_dir = f"../SysMoBench/output/compilation_check/tla/paxos_{selected_implementation}/local_file_gemini"
all_subdirs = [d for d in os.listdir(output_dir) if os.path.isdir(os.path.join(output_dir, d))]
latest_subdir = max(all_subdirs, key=lambda d: os.path.getmtime(os.path.join(output_dir, d)))
with open(f"{output_dir}/{latest_subdir}/result.json", "r", encoding="utf-8") as f:
    compilation_result = json.load(f)

output_dir = f"../SysMoBench/output/runtime_check/tla/paxos_{selected_implementation}/local_file_gemini"
all_subdirs = [d for d in os.listdir(output_dir) if os.path.isdir(os.path.join(output_dir, d))]
latest_subdir = max(all_subdirs, key=lambda d: os.path.getmtime(os.path.join(output_dir, d)))
with open(f"{output_dir}/{latest_subdir}/result.json", "r", encoding="utf-8") as f:
    runtime_result = json.load(f)

with open("prompts/fixing_prompt.txt", "r", encoding="utf-8") as f:
    fixing_prompt = f.read().format(tla_code=tla_code, cfg_code=cfg_code, selected_implementation=selected_implementation, syntax_errors = compilation_result, runtime_errors = runtime_result)

# Step 3: Use the Gemini API to generate a draft fix for the identified issues in the TLA+ specification. The generated content will be based on the provided prompt, which includes the original TLA+ code, configuration, and the results of the compilation and runtime checks. The draft fix will be expected to contain the corrected TLA+ specification and configuration that address the identified issues.
draft_fix = client.models.generate_content(
    model="gemini-3.5-flash",
    contents=fixing_prompt
)
draft_fix = draft_fix.text

print(f"GENERATED DRAFT FIX:\n{draft_fix}")

# Step 4: Parse the generated draft fix to separate the corrected TLA+ specification and configuration. The draft fix is expected to contain both the TLA+ model and the TLC configuration, which will be extracted and saved as separate files for further use in the verification process.
tla_model, tlc_config = map(str.strip, draft_fix.split("-- TLA END --", 1))

with open(f"generated_specs/paxos_{selected_implementation}/after_fixes/paxos_{selected_implementation}.tla", "w", encoding="utf-8") as f:
    f.write(tla_model)
with open(f"generated_specs/paxos_{selected_implementation}/after_fixes/paxos_{selected_implementation}.cfg", "w", encoding="utf-8") as f:
    f.write(tlc_config)
