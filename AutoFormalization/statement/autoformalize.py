import os
import re
import base64
import argparse
import random
import tqdm
import json

from copy import deepcopy
from AutoFormalization.utils import *
from E3.validator import Validator


def examples(dataset, category, num, reasoning):
    content = [{"type": "text", "text": 'Here are some examples:\n' if num > 1 else 'Here is an example:\n'}]

    indices = random.sample(range(1, 6), num)

    for idx in indices:
        input_text = ""
        if dataset == 'UniGeo':
            diagram2text_path = os.path.join(EXAMPLE_DIR, dataset, category, 'diagrams2texts', f'{idx}.txt')
            with open(diagram2text_path) as f:
                input_text += f.read().rstrip('\n') + ' '

        text_path = os.path.join(EXAMPLE_DIR, dataset, category, 'texts', f'{idx}.txt')
        with open(text_path) as f:
            input_text += f.read()

        formalization_path = os.path.join(EXAMPLE_DIR, dataset, category, 'formalizations', f'{idx}.lean')
        with open(formalization_path) as f:
            formalization = f.read()
            pattern = r"theorem\s?\w+\s?:\s?(.*?)\s?\:\="
            match = re.search(pattern, formalization, re.DOTALL)
            formal_statement = match.group(1)
            formal_statement = re.sub(r'\s+', ' ', formal_statement)

        if reasoning == 'multi-modal':
            image_path = os.path.join(EXAMPLE_DIR, dataset, category, 'diagrams', f'{idx}.png')
            image = process_image(image_path)
            content.append({"type": "image_url", "image_url": {"url": f"data:image/png;base64,{image}"}})
        
        content.append({"type": "text", "text": f'English Statement: {input_text}\nFormalized Statement: <<< {formal_statement} >>>\n'})
        
    return content


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dataset', type=str, choices=['Book', 'UniGeo'], required=True, help='Testing dataset')
    parser.add_argument('--category', type=str, nargs='+', choices=['', 'Parallel', 'Triangle', 'Quadrilateral', 'Congruent', 'Similarity'], required=True, help='Testing category')
    parser.add_argument('--reasoning', type=str, choices=['text-only', 'multi-modal'], required=True, help='Reasoning Type')
    parser.add_argument('--num_query', type=int, default=5, help='Maximum number of query per instance')
    parser.add_argument('--num_examples', type=int, default=0, help='Number of examples')
    args = parser.parse_args()

    random.seed(42)
    
    if args.dataset == 'UniGeo':
        if args.reasoning == 'multi-modal':
            instruction_head = 'Your task is to take a diagram and an English statement of a theorem from Euclidean Geometry and formalize it using Lean 4 programming language, adhering to the following structures and guidelines:\n'
        else:
            instruction_head = 'Your task is to take an English statement of a theorem from Euclidean Geometry and formalize it using Lean 4 programming language, adhering to the following structures and guidelines:\n'
    else:
        if args.reasoning == 'multi-modal':
            instruction_head = 'Your task is to take a diagram and an English statement of a theorem from Euclidean Geometry (proof is omitted using the <prf> symbol) and formalize it using Lean 4 programming language, adhering to the following structures and guidelines:\n'
        else:
            instruction_head = 'Your task is to take an English statement of a theorem from Euclidean Geometry (proof is omitted using the <prf> symbol) and formalize it using Lean 4 programming language, adhering to the following structures and guidelines:\n'
    
    with open('instruction.txt') as f:
        instruction = instruction_head + f.read()
    
    for c in args.category:
        print('Category: ', c)
        validator = Validator(tmp_path=os.path.join(ROOT_DIR, "tmp", "validate", args.dataset, args.reasoning, str(args.num_examples)+"-shot",  c))
        result_dir = os.path.join(ROOT_DIR, "result", "statement", args.dataset, args.reasoning, str(args.num_examples)+"shot", c)
        os.makedirs(result_dir, exist_ok=True)

        example_content = []
        if args.num_examples > 0:
            example_content = examples(args.dataset, c, args.num_examples, args.reasoning)

        if args.dataset == 'UniGeo':
            testing_idx = range(1, 21)
        else:
            testing_idx = [i for i in range(1, 49) if i not in [2, 6, 12, 32, 42]]
                
        for i in tqdm.tqdm(testing_idx):
            model = GPT4(model="gpt-4-vision-preview" if args.reasoning == 'multi-modal' else "gpt-4-1106-preview")
            content = deepcopy(example_content)
            
            problem_text = ""
            if args.dataset == 'UniGeo':
                diagram2text_path = os.path.join(ROOT_DIR, args.dataset, c, 'diagrams2texts', f'{i}.txt')
                with open(diagram2text_path) as f:
                    problem_text += f.read().rstrip('\n') + ' '
            
            text_path = os.path.join(ROOT_DIR, args.dataset, c, 'texts', f'{i}.txt')
            with open(text_path) as f:
                problem_text += f.read()

            file_name = f'Prop{i:02d}.lean' if args.dataset == 'Book' else f'Thm{i:02d}.lean'
            formalization_path = os.path.join(ROOT_DIR, args.dataset, c, file_name)
            with open(formalization_path) as f:
                formalization = f.read()
                pattern = r"theorem\s?\w+\s?:\s?(.*?)\s?\:\="
                match = re.search(pattern, formalization, re.DOTALL)
                formal_statement = match.group(1)
                formal_statement = re.sub(r'\s+', ' ', formal_statement)

            content.append({"type": "text", "text": f'Here is your problem:\n'})

            if args.reasoning == 'multi-modal':
                image_path = os.path.join(ROOT_DIR, args.dataset, c, 'diagrams', f'{i}.png')
                image = process_image(image_path)
                content.append({"type": "image_url", "image_url": {"url": f"data:image/png;base64,{image}"}})
                
            content.append({"type": "text", "text": f'English Statement: {problem_text}\nFormalized Statement: '})

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
                        pred = re.sub(r'\s+', ' ', pred).strip()
                        error_message = validator.validate(pred, str(i))
                        if error_message is None:
                            result_file = os.path.join(result_dir, str(i)+'.json')
                            with open(result_file, 'w', encoding='utf-8') as f:
                                json.dump({'prediction': pred, 'groud_truth': formal_statement}, f, ensure_ascii=False)
                            break
                        else:
                            model.add_message("assistant", response)
                            model.add_message("user", lean_error(error_message))
                    else:
                        model.add_message("assistant", response)
                        model.add_message("user", parse_error())


if __name__ == "__main__":
    main()