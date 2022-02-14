from LassyExtraction.milltypes import WordType, AtomicType, FunctorType, DiamondType, BoxType, PolarizedType
from LassyExtraction.aethel import ProofNet, ProofFrame, Premise
from typing import Dict, List, Set, Tuple
from LassyExtraction.aethel import (Term, Var, Lex, Application, Abstraction,
                                    BoxIntro, BoxElim, DiamondIntro, DiamondElim, ProofNet, ProofFrame,
                                    AxiomLinks, WordType, FunctorType, PolarizedType, ModalType, EmptyType)
from LassyExtraction.milltypes import polarize_and_index
from LassyExtraction.proofs import get_result, ProofError
from collections import OrderedDict
from tqdm import tqdm


def unique_types(input: List[ProofNet], name: str):
    """Calculates the percentage of unique types of a list of ProofNet"""
    unique_set = set([tuple(thing.proof_frame.get_types()) for thing in input])
    print(f"{(len(unique_set) / len(input))} percent of {name} is unique")
    return len(unique_set) / len(input)

def unique_dict(input: List[ProofNet]):
    """Creates a dictionary with all different ProofNets and number of occurrences"""
    dict_types = {}
    unique_cnt = 0
    counter = 1
    for proofnet in input:
        counter += 1
        if counter % 1000 == 0:
            #print(f"For {counter} ProofNets, there are {len(dict_types)} different type sequences")
            print(f"{counter}, {len(dict_types)}")
            for val in dict_types.values():
                if val == 1:
                    unique_cnt += 1
            #print(unique_cnt)
            unique_cnt = 0
        types = tuple(proofnet.proof_frame.get_types())
        if types in dict_types.keys():
            dict_types[types] += 1
        else:
            dict_types[types] = 1


    dict_types = OrderedDict(sorted(dict_types.items(), key=lambda x:x[1], reverse=True))
    return dict_types

def translation(x: WordType, atom_translation: dict[str, str], dep_translation: dict[str, str]) -> WordType:
    """Translates a WordType based on the atomic and dependency translations"""
    if isinstance(x, PolarizedType):
        idx, polarity = x.index, x.polarity
        if x.type in atom_translation.keys():
            _type = atom_translation[x.type]
        else:
            _type = x.type
        return PolarizedType(_type, polarity, idx)
    if isinstance(x, AtomicType):
        if x.type in atom_translation.keys():
            return AtomicType(atom_translation[x.type])
        else:
            return x
    if isinstance(x, FunctorType):
        result = translation(x.result, atom_translation, dep_translation)
        argument = translation(x.argument, atom_translation, dep_translation)
        return FunctorType(argument, result)
    if isinstance(x, DiamondType):
        content = translation(x.content, atom_translation, dep_translation)
        modality = x.modality
        if modality in dep_translation.keys():
            modality = dep_translation[modality]
        return DiamondType(content, modality)
    elif isinstance(x, BoxType):
        content = translation(x.content, atom_translation, dep_translation)
        modality = x.modality
        if modality in dep_translation.keys():
            modality = dep_translation[modality]
        return BoxType(content, modality)
    raise TypeError(f"i dont know what to do with this: {type(x)}")


def list_translation(xs: List[WordType], atom_translation: dict[str, str], dep_translation: dict[str, str]) \
        -> List[WordType]:
    """Translates a list of WordTypes based on the atomic and dependency translations"""
    return [translation(x, atom_translation, dep_translation) for x in xs]


def translate_net(pn: ProofNet, atom_translation: dict[str, str], dep_translation: dict[str, str]) -> ProofNet:
    """Translates a ProofNet based on the atomic and dependency translations"""
    return ProofNet(translate_frame(pn.proof_frame, atom_translation, dep_translation), pn.axiom_links, pn.name)


def translate_frame(pf: ProofFrame, atom_translation: dict[str, str], dep_translation: dict[str, str]) -> ProofFrame:
    """Translates a ProofFrame based on the atomic and dependency translations"""
    conclusion = translation(pf.conclusion, atom_translation, dep_translation)
    premises = [translate_premise(premise, atom_translation, dep_translation) for premise in pf.premises]
    return ProofFrame(premises, conclusion)


def translate_premise(p: Premise, atom_translation: dict[str, str], dep_translation: dict[str, str]) -> Premise:
    """Translates a Premise based on the atomic and dependency translations"""
    premise_type = translation(p.type, atom_translation, dep_translation)
    return Premise(p.word, premise_type)


def is_mod(functor: Term) -> bool:
    """Checks whether a Term is a modifier"""
    if isinstance(functor, BoxElim):
        if functor.box == "mod" or functor.box == "predm" or functor.box == "app":
            return not mandatory_mod(functor)
    return False


def mandatory_mod(functor: BoxElim) -> bool:
    """Checks whether a modifier in mandatory"""
    body = functor.body
    return isinstance(body, DiamondElim) and body.diamond == functor.box

def remove_all_mods(term: Term) -> Term:
    """Return the input Term with all modifiers removed from it"""
    if isinstance(term, Var):
        return term
    if isinstance(term, Lex):
        return term
    if isinstance(term, Application):
        functor = term.functor
        argument = term.argument
        if is_mod(functor):
            return remove_all_mods(argument)
        else:
            functor = remove_all_mods(functor)
            argument = remove_all_mods(argument)
            return Application(functor, argument)
    if isinstance(term, Abstraction):
        body = remove_all_mods(term.body)
        return Abstraction(body, term.abstraction.idx)
    if isinstance(term, BoxIntro):
        body = remove_all_mods(term.body)
        return BoxIntro(body, term.box)
    if isinstance(term, BoxElim):
        body = remove_all_mods(term.body)
        return BoxElim(body)
    if isinstance(term, DiamondIntro):
        body = remove_all_mods(term.body)
        return DiamondIntro(body, term.diamond)
    if isinstance(term, DiamondElim):
        body = remove_all_mods(term.body)
        return DiamondElim(body)


def return_all_mods(term: Term) -> list[Term]:
    """Return the input Term with all variants of modifiers"""
    if isinstance(term, Var):
        return [term]
    if isinstance(term, Lex):
        return [term]
    if isinstance(term, Application):
        functor = term.functor
        argument = term.argument
        if is_mod(functor):
            return return_all_mods(argument) + \
                   [Application(f, a) for f in return_all_mods(functor) for a in return_all_mods(argument)]
        else:
            return [Application(f, a) for f in return_all_mods(functor) for a in return_all_mods(argument)]
    if isinstance(term, Abstraction):
        return [Abstraction(b, term.abstraction.idx) for b in return_all_mods(term.body)]
    if isinstance(term, BoxIntro):
        return [BoxIntro(b, term.box) for b in return_all_mods(term.body)]
    if isinstance(term, BoxElim):
        return [BoxElim(b) for b in return_all_mods(term.body)]
    if isinstance(term, DiamondIntro):
        return [DiamondIntro(b, term.diamond) for b in return_all_mods(term.body)]
    if isinstance(term, DiamondElim):
        return [DiamondElim(b) for b in return_all_mods(term.body)]
    raise TypeError(f"Something goes wrong with the type: {type(term)}")


def participating_ids(term: Term) -> Set[int]:
    """Returns the indices of participating premises based on the term"""
    if isinstance(term, Var):
        return set()
    if isinstance(term, Lex):
        return {term.idx}
    if isinstance(term, Application):
        functor = participating_ids(term.functor)
        argument = participating_ids(term.argument)
        return functor.union(argument)
    if isinstance(term, Abstraction):
        body = participating_ids(term.body)
        return body
    return participating_ids(term.body)


def term_to_axiom_links(term: Term, proof_frame: ProofFrame) -> AxiomLinks:
    """Create new axiom links using the Term and ProofFramse"""
    idx = -500

    def get_type_from_premise(idx: int) -> WordType:
        """Returns the WordType using the index of the premise"""
        return proof_frame.premises[idx].type

    def invert_polarity(hatted: WordType) -> WordType:
        """Invert the polarity of hatted types"""
        if isinstance(hatted, FunctorType):
            hatted_arg = invert_polarity(hatted.argument)
            hatted_res = invert_polarity(hatted.result)
            return FunctorType(hatted_arg, hatted_res)
        if isinstance(hatted, PolarizedType):
            return PolarizedType(hatted.type, not hatted.polarity, hatted.index)
        if isinstance(hatted, ModalType):
            return type(hatted)(invert_polarity(hatted.content), hatted.modality)
        raise TypeError(f"{hatted, type(hatted)}")

    def create_axiomlinks(_term: Term, index: int) -> tuple[AxiomLinks, WordType, dict[int, WordType], int]:
        """Create axiom links based on the term"""
        if isinstance(_term, Var):
            index, new_hat_type = polarize_and_index(_term.t(), True, index)
            return set(), new_hat_type, {_term.idx: new_hat_type}, index
        if isinstance(_term, Lex):
            return set(), get_type_from_premise(_term.idx), dict(), index
        if isinstance(_term, Application):
            axiomlinks_arg, output_arg, var_arg, index = create_axiomlinks(_term.argument, index)
            axiomlinks_func, output_func, var_func, index = create_axiomlinks(_term.functor, index)
            axiomlinks = axiomlinks_arg.union(axiomlinks_func)
            for atom_arg, atom_func in zip(output_arg, output_func):
                axiom_link = (atom_arg.index, atom_func.index) if atom_arg.polarity else (
                atom_func.index, atom_arg.index)
                axiomlinks.add(axiom_link)
            return axiomlinks, get_result(output_func), {**var_arg, **var_func}, index
        if isinstance(_term, Abstraction):
            axiomlinks, output, variables, index = create_axiomlinks(_term.body, index)
            new_hat_type = variables.pop(_term.abstraction.idx)
            new_output = FunctorType(invert_polarity(new_hat_type), output)
            return axiomlinks, new_output, variables, index
        if isinstance(_term, (DiamondElim, DiamondIntro, BoxElim, BoxIntro)):
            return create_axiomlinks(_term.body, index)
        raise TypeError(f'Something goes wrong with the type: {type(_term)}')

    axiom_links, output_type, _, _ = create_axiomlinks(term, idx)
    axiom_links.add((output_type.index, proof_frame.conclusion.index))

    # Delete the negative detours so that there collapsed into usable axiom links
    # So for example,  (x, -500), (-500, y) becomes (x,y)
    def negative_detours(axiom_links: AxiomLinks) -> AxiomLinks:
        result_links = axiom_links.copy()
        # Loop through axiom links to find a match between the left and right side of a tuple
        for left, right in axiom_links:
            for links, rechts in axiom_links:
                if right == links:
                    result_links.add((left, rechts))
                    result_links.remove((links, rechts))
                    result_links.remove((left, right))
                    # After changing the result_link, use these as input recursively
                    result_links = negative_detours(result_links)
                    # Then return the resulting axiom links
                    return result_links
        # In case there are no axiom links that can be collapsed, return the resulting links
        return result_links

    # Create the axiom links by collapsing all axiom links with a negative detour in it using "negative_detours"
    neg_links = {(left, right) for left, right in axiom_links if left < 0 or right < 0}
    neg_axioms = negative_detours(neg_links)
    axiom_links = (axiom_links - neg_links).union(neg_axioms)
    return axiom_links

### Make the new Proofnet for the unmodded data
def _remove_all_mods(pn: ProofNet) -> ProofNet:
    """Removes the modifiers of a ProofNets (unmodding)"""
    removed_term = remove_all_mods(pn.get_term())
    # an ordered subset of the original PF obtained from participating_ids:
    removed_premises = [pn.proof_frame.premises[i] for i in participating_ids(removed_term)]
    removed_pf = ProofFrame(removed_premises, pn.proof_frame.conclusion)
    removed_axiom_links = term_to_axiom_links(removed_term, pn.proof_frame)
    return ProofNet(removed_pf, removed_axiom_links, pn.name)

def _return_all_mods(pn: ProofNet) -> List[ProofNet]:
    """Returns a list of ProofNets with all variants of modifiers (partial unmodding)"""
    removed_nets = []
    removed_terms = return_all_mods(pn.get_term())
    for removed_term in removed_terms:
        removed_premises = [pn.proof_frame.premises[i] for i in participating_ids(removed_term)]
        removed_pf = ProofFrame(removed_premises, pn.proof_frame.conclusion)
        removed_axiom_links = term_to_axiom_links(removed_term, pn.proof_frame)
        removed_nets.append(ProofNet(removed_pf, removed_axiom_links, pn.name))
    return removed_nets


### Sanity check for whether term_to_axiom_links returns the original proofframe, for a list of ProofNets
def sanity_check_axiom_links(pns: list[ProofNet]):
    """Checks whether the newly generated axiom links (of a list of ProofNets) are the same as the original ones"""
    right = []
    wrong = []
    key_error = {}
    proof_error = {}
    counter = 0
    for pn in pns:
        try:
            new_axioms = term_to_axiom_links(pn.get_term(), pn.proof_frame)
            original_axioms = pn.axiom_links
            if not new_axioms == original_axioms:
                wrong.append(counter)
                counter += 1
                continue
            else:
                right.append(counter)
                counter += 1
        except KeyError as e:
            key_error[counter] = e
            counter += 1
            continue
        except ProofError as es:
            proof_error[counter] = es
            counter += 1
            continue
    return right, wrong, key_error, proof_error


### Sanity check for whether term_to_axiom_links returns the original proofframe, for a single ProofNets
def sanity_check_axioms(pn: ProofNet):
    """Checks whether the newly generated axiom links of a single ProofNet are the same as the original ones"""

    new_axioms = term_to_axiom_links(pn.get_term(), pn.proof_frame)
    original_axioms = pn.axiom_links
    if not new_axioms == original_axioms:
        raise TypeError(f"Error, axiomslinks are not the same, \n new: {new_axioms} \n original: {original_axioms}")


def get_solutions(input) -> dict[tuple[WordType, ...], set[Term]]:
    """Creates a dictionary from type sequence with all corresponding terms of the partial unmodded sentences"""
    solutions = {}
    for proofnet in tqdm(input):
        if len(proofnet.proof_frame) < 20:
            try:
                all_modded = _return_all_mods(proofnet)
            except AssertionError:
                continue
        else:
            try:
                all_modded = [proofnet, _remove_all_mods(proofnet)]
            except AssertionError:
                continue
        for each in all_modded:
            each = canonicalise(each)
            frame = tuple(each.proof_frame.get_types())
            term = each.get_term()
            if frame in solutions.keys():
                solutions[frame].add(term)
            else:
                solutions[frame] = {term}
    return solutions

def get_sol(input) -> dict[tuple[WordType, ...], set[Term]]:
    """Creates a dictionary from type sequence with all corresponding terms of the unmodded sentences"""
    solutions = {}
    for proofnet in tqdm(input):
        try:
            all_modded = [_remove_all_mods(proofnet)]
        except AssertionError:
            continue
        for each in all_modded:
            each = canonicalise(each)
            frame = tuple(each.proof_frame.get_types())
            term = each.get_term()
            if frame in solutions.keys():
                solutions[frame].add(term)
            else:
                solutions[frame] = {term}
    return solutions

def get_solu(input) -> dict[tuple[WordType, ...], set[Term]]:
    """Creates a dictionary from type sequence with all corresponding terms"""
    solutions = {}
    for proofnet in tqdm(input):
       proofnet = canonicalise(proofnet)
       frame = tuple(proofnet.proof_frame.get_types())
       term = proofnet.get_term()
       if frame in solutions.keys():
           solutions[frame].add(term)
       else:
           solutions[frame] = {term}
    return solutions

def canonicalise(pn: ProofNet) -> ProofNet:
    """Canonicalises indices of a ProofNet"""
    def canonicalise_frame(pf: ProofFrame) -> tuple[ProofFrame, dict[int, int]]:
        atom_translation, new_premises = {}, []

        def canonicalise_premise(premise: Premise, _start_from: int) -> tuple[Premise, int]:
            type, start_from = canonicalise_type(premise.type, _start_from)
            return Premise(word=premise.word, type=type), start_from

        def canonicalise_type(wordtype: WordType, _start_from: int) -> tuple[WordType, int]:
            if isinstance(wordtype, PolarizedType):
                old_idx = wordtype.index
                new_idx = _start_from
                atom_translation[old_idx] = new_idx
                _start_from += 1
                #print(wordtype, PolarizedType(wordtype.type, wordtype.polarity, new_idx), _start_from)
                return PolarizedType(wordtype.type, wordtype.polarity, new_idx), _start_from
            if isinstance(wordtype, FunctorType):
                argument, _start_from = canonicalise_type(wordtype.argument, _start_from)
                result, _start_from = canonicalise_type(wordtype.result, _start_from)
                return FunctorType(argument, result), _start_from
            if isinstance(wordtype, BoxType):
                content, _start_from = canonicalise_type(wordtype.content, _start_from)
                return BoxType(content, wordtype.modality), _start_from
            if isinstance(wordtype, DiamondType):
                content, _start_from = canonicalise_type(wordtype.content, _start_from)
                return DiamondType(content, wordtype.modality), _start_from
            if isinstance(wordtype, EmptyType):
                #print(f"{wordtype} is EmptyType")
                return wordtype, _start_from
            else:
                print(f"There is something of type {wordtype}")

        start_from = 0
        for old_premise in pf.premises:
            new_premise, start_from = canonicalise_premise(old_premise, start_from)
            new_premises.append(new_premise)

        atom_translation[pf.conclusion.index] = start_from
        new_conclusion = PolarizedType(pf.conclusion.type, pf.conclusion.polarity, start_from)
        #print(atom_translation)
        return ProofFrame(premises=new_premises, conclusion=new_conclusion), atom_translation

    def canonicalise_links(oldlinks: AxiomLinks, atom_translation: dict[int, int]) -> AxiomLinks:
        new_links = set()
        for left, right in oldlinks:
            new_links.add((atom_translation[left], atom_translation[right]))
        return new_links

    new_frame, old_to_new = canonicalise_frame(pn.proof_frame)
    return ProofNet(new_frame, canonicalise_links(pn.axiom_links, old_to_new), pn.name)


