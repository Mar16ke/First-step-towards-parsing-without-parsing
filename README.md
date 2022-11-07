# A First Step Towards Parsing Without Parsing

This is the repository for the project "*Simplifying and expanding the ÆTHEL dataset by type conversion and modifying modifiers: A first step towards parsing without parsing*". 

## **About project**
Parsing sentences and their proofs consist of type assignment and proof construction. Previous work on the AETHEL dataset raises the question whether it could be sufficient to have a mapping from type-sequences to derivations, instead of proof construction. Since such a mapping is easier with a smaller variation of proofs, this work aims to modify the AETHEL dataset to be less diverse, as a step towards parsing without parsing. I present: (1) two methods to decrease the percentage of unique proof frames: type conversion and modifying modifiers; (2) new datasets obtained from these methods. With type conversion, atomic types and dependency markers were converted into more general types to simplify the proof frames. Subsequently, the dataset was modified to either have modifiers removed from the sentences (unmodding) or to have sentences of all variations of modifiers (partial unmodding). The results showed a decrease in unique proof frames and a substantial amount of proofs from a test already in the training set. Although the unmodding and partial unmodding dataset are not yet perfect, they are useful new datasets, especially for further analysis on modifiers. This work shows the first step towards parsing without parsing and can be build upon for future work on mapping type-sequences to derivations.

## **Usage**

**Installation**

Python 3.9+

To run the code:

1. First download the code from the [Lassy extraction](https://github.com/konstantinosKokos/lassy-tlg-extraction) (read the README for more information) and unzip
2. Download the main.py from this repository and put this in the LassyExtraction folder. 

You can access the original dataset by running:

```
>>> import pickle
>>> with open('./data/train_dev_test_0.4.dev0.p', 'rb') as f:
...    train, dev, test = pickle.load(f) 
```

An example of how to use the code for type conversion and modifying modifiers is shown below.

```
atom_convert = {"N": "NP", "VNW": "NP", "WW": "NP", "SPEC": "NP", "TW": "NP", "SSUB": "S", "SMAIN":"S"}
dep_convert = {"app": "mod", "predm": "mod"}
pns_conversion = []

for sent in pns:
    new_sent = translate_net(sent, atom_convert, dep_convert)
    pns_conversion.append(new_sent)
```

```
unmodded_list = []

for proofnet in pns:
    try:
        unmodded = _remove_all_mods(proofnet)
        unmodded = canonicalise(unmodded)
        unmodded_list.append(unmodded) 
    except AssertionError:
		continue
```

