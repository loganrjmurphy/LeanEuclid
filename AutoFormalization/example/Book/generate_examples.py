import os
import random
import shutil

from E3.utils import ROOT_DIR

def main():
    random.seed(24)

    # os.makedirs(f'diagrams', exist_ok=True)
    # os.makedirs(f'texts', exist_ok=True)
    # os.makedirs(f'formalizations', exist_ok=True)
    os.makedirs(f'texts_proofs', exist_ok=True)

    sampled_idx = [2,6,12,32,42]

    for i, idx in enumerate(sampled_idx):
        # original_img_path = f'../../Book/diagrams/{idx}.png'
        # img_path = f'diagrams/{i+1}.png'
        # shutil.copy(original_img_path, img_path)

        # original_text_path = f'../../Book/texts/{idx}.txt'
        # text_path = f'texts/{i+1}.txt'
        # shutil.copy(original_text_path, text_path)

        # original_formalization_path = f'../../Book/Prop{idx:02d}.lean'
        # formalization_path = f'formalizations/{i+1}.lean'
        # shutil.copy(original_formalization_path, formalization_path)

        original_text_path = os.path.join(ROOT_DIR, "Book", "texts_proofs", f'{idx}.txt')
        text_path = f'texts_proofs/{i+1}.txt'
        shutil.copy(original_text_path, text_path)


if __name__ == "__main__":
    main()
