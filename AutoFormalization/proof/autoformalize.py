import os
import re
import argparse
import random
import tqdm
import json

from copy import deepcopy
from AutoFormalization.utils import *


def preceding_propositions(idx):
    with open(
        "AutoFormalization/proof/book_propositions.json", "r", encoding="utf-8"
    ) as f:
        propositions = json.load(f)
    pre_props = []
    for i in range(1, idx):
        props = propositions[str(i)]
        for prop in props:
            pre_props.append("axiom " + prop)

    return "\n".join(pre_props)


def examples(dataset, category, num, reasoning):
    content = [
        {
            "type": "text",
            "text": "Here are some examples:\n" if num > 1 else "Here is an example:\n",
        }
    ]

    indices = random.sample(range(1, 6), num)

    for idx in indices:
        if dataset == "UniGeo":
            input_text = ""
            diagram2text_path = os.path.join(
                EXAMPLE_DIR, dataset, category, "diagrams2texts", f"{idx}.txt"
            )
            with open(diagram2text_path) as f:
                input_text += f.read().rstrip("\n") + " "

            text_path = os.path.join(
                EXAMPLE_DIR, dataset, category, "texts", f"{idx}.txt"
            )
            with open(text_path) as f:
                input_text += f.read()

            informal_proof_path = os.path.join(
                EXAMPLE_DIR, dataset, category, "proofs", f"{idx}.txt"
            )
            with open(informal_proof_path) as f:
                informal_proof = f.read().rstrip("\n")
                informal_proof = re.sub(r"\n", ", ", informal_proof) + "."
        else:
            text_proof_path = os.path.join(
                EXAMPLE_DIR, dataset, category, "texts_proofs", f"{idx}.txt"
            )
            with open(text_proof_path) as f:
                text_proof = f.read()

        formalization_path = os.path.join(
            EXAMPLE_DIR, dataset, category, "formalizations", f"{idx}.lean"
        )
        with open(formalization_path) as f:
            formalization = f.read()
            pattern = r"theorem\s?\w+\s?:\s?(.*?)\s?\:\="
            match = re.search(pattern, formalization, re.DOTALL)
            formal_statement = match.group(1)
            formal_statement = re.sub(r"\s+", " ", formal_statement)

            pattern = r"theorem.*?:=\s*\n*by\s*(.*?)(?=theorem|end|$)"
            match = re.search(pattern, formalization, re.DOTALL)
            formal_proof = match.group(1)
            formal_proof = re.sub(r"\n\n", "\n", formal_proof)

        if reasoning == "multi-modal":
            image_path = os.path.join(
                EXAMPLE_DIR, dataset, category, "diagrams", f"{idx}.png"
            )
            image = process_image(image_path)
            content.append(
                {
                    "type": "image_url",
                    "image_url": {"url": f"data:image/png;base64,{image}"},
                }
            )

        if dataset == "UniGeo":
            content.append(
                {
                    "type": "text",
                    "text": f"English Statement: {input_text}\nEnglish Proof: {informal_proof}\nFormalized Statement: {formal_statement}\nFormalized Proof: <<< {formal_proof} >>>\n",
                }
            )
        else:
            content.append(
                {
                    "type": "text",
                    "text": f"English Statement and Proof: {text_proof}\nFormalized Statement: {formal_statement}\nFormalized Proof: <<< {formal_proof} >>>\n",
                }
            )

    return content


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--dataset",
        type=str,
        choices=["Book", "UniGeo"],
        required=True,
        help="Testing dataset",
    )
    parser.add_argument(
        "--category",
        type=str,
        nargs="+",
        choices=[
            "",
            "Parallel",
            "Triangle",
            "Quadrilateral",
            "Congruent",
            "Similarity",
        ],
        required=True,
        help="Testing category",
    )
    parser.add_argument(
        "--reasoning",
        type=str,
        choices=["text-only", "multi-modal"],
        required=True,
        help="Reasoning Type",
    )
    parser.add_argument(
        "--num_query", type=int, default=5, help="Maximum number of query per instance"
    )
    parser.add_argument(
        "--num_examples", type=int, default=0, help="Number of examples"
    )
    args = parser.parse_args()

    random.seed(42)

    if args.reasoning == "multi-modal":
        instruction_head = "Your task is to formalize a proof of a theorem from Euclidean Geometry using the Lean 4 programming language, based on its diagram, English statement and proof, and formalized statement. The formalization should adhere to predefined structures and guidelines detailed below.\n"
    else:
        instruction_head = "Your task is to formalize a proof of a theorem from Euclidean Geometry using the Lean 4 programming language, based on its English statement and proof, and formalized statement. The formalization should adhere to predefined structures and guidelines detailed below.\n"

    with open(f"AutoFormalization/proof/{args.dataset.lower()}_instruction.txt") as f:
        instruction = instruction_head + f.read()

    for c in args.category:
        print("Category: ", c)
        result_dir = os.path.join(
            ROOT_DIR,
            "result",
            "proof",
            args.dataset,
            args.reasoning,
            str(args.num_examples) + "shot",
            c,
        )
        os.makedirs(result_dir, exist_ok=True)

        example_content = []
        if args.num_examples > 0:
            example_content = examples(
                args.dataset, c, args.num_examples, args.reasoning
            )

        if args.dataset == "UniGeo":
            namespace = f"UniGeo.{c}"
            testing_idx = range(1, 21)
        else:
            namespace = "Elements.Book1"
            testing_idx = [i for i in range(1, 49) if i not in [2, 6, 12, 32, 42]]

        for i in tqdm.tqdm(testing_idx):
            model = GPT4(
                model=(
                    "gpt-4-vision-preview"
                    if args.reasoning == "multi-modal"
                    else "gpt-4-1106-preview"
                )
            )
            content = deepcopy(example_content)

            if args.dataset == "UniGeo":
                input_text = ""
                diagram2text_path = os.path.join(
                    ROOT_DIR, args.dataset, c, "diagrams2texts", f"{i}.txt"
                )
                with open(diagram2text_path) as f:
                    input_text += f.read().rstrip("\n") + " "

                text_path = os.path.join(ROOT_DIR, args.dataset, c, "texts", f"{i}.txt")
                with open(text_path) as f:
                    input_text += f.read()

                informal_proof_path = os.path.join(
                    ROOT_DIR, args.dataset, c, "proofs", f"{i}.txt"
                )
                with open(informal_proof_path) as f:
                    informal_proof = f.read().rstrip("\n")
                    informal_proof = re.sub(r"\n", ", ", informal_proof) + "."
            else:
                instruction = instruction.replace(
                    r"{PRECEDING_PROPOSITIONS}", preceding_propositions(i)
                )
                text_proof_path = os.path.join(
                    ROOT_DIR, args.dataset, c, "texts_proofs", f"{i}.txt"
                )
                with open(text_proof_path) as f:
                    text_proof = f.read()

            file_name = (
                f"Prop{i:02d}.lean" if args.dataset == "Book" else f"Thm{i:02d}.lean"
            )
            formalization_path = os.path.join(ROOT_DIR, args.dataset, c, file_name)
            with open(formalization_path) as f:
                formalization = f.read()
                pattern = r"theorem\s?\w+\s?:\s?(.*?)\s?\:\="
                match = re.search(pattern, formalization, re.DOTALL)
                formal_statement = match.group(1)
                formal_statement = re.sub(r"\s+", " ", formal_statement)

            content.append({"type": "text", "text": f"Here is your problem:\n"})

            if args.reasoning == "multi-modal":
                image_path = os.path.join(
                    ROOT_DIR, args.dataset, c, "diagrams", f"{i}.png"
                )
                image = process_image(image_path)
                content.append(
                    {
                        "type": "image_url",
                        "image_url": {"url": f"data:image/png;base64,{image}"},
                    }
                )

            if args.dataset == "UniGeo":
                content.append(
                    {
                        "type": "text",
                        "text": f"English Statement: {input_text}\nEnglish Proof: {informal_proof}\nFormalized Statement: {formal_statement}\nFormalized Proof: ",
                    }
                )
            else:
                content.append(
                    {
                        "type": "text",
                        "text": f"English Statement and Proof: {text_proof}\nFormalized Statement: {formal_statement}\nFormalized Proof: ",
                    }
                )

            model.add_message("system", instruction)
            model.add_message("user", content)

            for _ in range(args.num_query):
                try:
                    response = model.get_response()
                except Exception as e:
                    print(f"An error occurred: {e}")

                if response:
                    pattern = r"<<<(.*?)>>>"
                    match = re.search(pattern, response, re.DOTALL)

                    if match:
                        pred = match.group(1)
                        pred = pred.strip()
                        result_file = os.path.join(result_dir, str(i) + ".lean")
                        with open(result_file, "w") as f:
                            lean_file = format_content(
                                args.dataset,
                                namespace,
                                f"formalized_theorem_{i}",
                                formal_statement,
                                pred,
                            )
                            f.write(lean_file)
                        break
                    else:
                        model.add_message("assistant", response)
                        model.add_message("user", parse_error())


if __name__ == "__main__":
    main()
