"""Benchmark inputs, checked dependencies and candidate validation."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / 'benchmarks'
TARGETS = ('preHorners', 'Horners', 'interchange_2x2', 'monitor', 'contour_row', 'contour_right')
FOUNDATIONS = {'functional_extensionality_dep', 'propositional_extensionality'}

def uncomment(text):
    """Remove nested Coq comments while preserving strings."""
    out, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        pair = text[i:i+2]
        if not quoted and pair == '(*':
            depth += 1
            out.append(' ')
            i += 2
        elif depth and pair == '*)':
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            if text[i] == '"':
                if quoted and pair == '""':
                    out.extend(pair)
                    i += 2
                    continue
                quoted = not quoted
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Coq comment')
    return ''.join(out)
TACTICS = {'intros', 'intro', 'induction', 'simpl', 'rewrite', 'reflexivity',
           'exact', 'apply', 'assumption', 'norm_right', 'norm_left',
           'series_rewrite', 'series_rewrite_rev', 'series_rewrite_lhs',
           'series_rewrite_lhs_rev', 'series_rewrite_rhs', 'series_rewrite_rhs_rev',
           'series_reflexivity', 'snd_para_at', 'fst_para_at'}


FORBIDDEN = {'admitted', 'admit', 'give_up', 'abort', 'axiom', 'axioms',
             'parameter', 'parameters', 'hypothesis', 'hypotheses',
             'native_cast_no_check', 'vm_cast_no_check', 'exact_no_check',
             'abstract', 'ltac', 'ltac2', 'load', 'require', 'import', 'export',
             'set', 'unset', 'declare', 'redirect', 'definition', 'lemma',
             'theorem', 'opaque', 'transparent'}


def tokens(text):
    return re.findall(r'[A-Za-z_][A-Za-z_0-9\x27]*|[^\s]', text)


def screen(candidate, declaration, *, allowed_tactics=TACTICS):
    try:
        clean = uncomment(candidate).strip()
    except ValueError:
        return None, 'malformed_comment'
    if '"' in clean:
        return None, 'strings_not_supported'
    match = re.fullmatch(r'(Lemma\s+\w+\s*:.*?)\bProof\s*\.(.*?)\bQed\s*\.', clean, re.S)
    if not match:
        return None, 'incomplete_or_extra_commands'
    if tokens(match[1]) != tokens(declaration):
        return None, 'statement_changed'
    body = match[2]
    if FORBIDDEN.intersection(word.lower() for word in tokens(body)):
        return None, 'forbidden_proof_command'
    # Qualified identifiers have dots without following whitespace; sentence
    # terminators must have whitespace/end. Deliberately restricted grammar.
    for command in re.split(r'\.(?=\s|$)', body):
        command = re.sub(r'^[\s\-+*{}]+', '', command).strip()
        if command and (not tokens(command) or tokens(command)[0] not in allowed_tactics):
            return None, 'unsupported_tactic_or_vernacular'
    if body.strip() and not body.rstrip().endswith('.'):
        return None, 'missing_tactic_terminator'
    # Construct the checked theorem with the trusted declaration, never the
    # submitted declaration, after token-preserving comparison.
    return declaration + '\nProof.\n' + body + '\nQed.\n', None
POLICY = TACTICS | {
    'rel_ext', 'unfold', 'destruct', 'exists', 'split', 'subst', 'auto',
    'eapply', 'eauto', 'assert', 'transitivity', 'symmetry', 'replace', 'lia',
    'cbn', 'pose', 'repeat', 'f_equal', 'congruence', 'try', 'change', 'fold'}


PROOF_WORDS = re.compile(r'\b(?:Proof|Qed|Defined|Admitted|Abort)\s*\.|\bLtac2?\b')


PAPER_IMPLEMENTATION = re.compile(
    r'\b(?:Coq|Rocq|Ltac|eq_rect|cast_rel|P_as_PP|Hpush_pow|det_PP|'
    r'intros|reflexivity|series_rewrite\w*|norm_left|norm_right)\b')


PROOF_LINE = re.compile(
    r'(?m)^\s*(?:intros?|rewrite|apply|exact|assert|unfold|cbn|simpl|'
    r'series_rewrite\w*|reflexivity|admit)\b[^\n]*\.\s*$')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reviewed_path(name):
    path = ROOT / name
    if Path(name).is_absolute() or '..' in Path(name).parts:
        raise ValueError('Input must be repository-relative')
    if Path(name).parts[0] not in {'benchmarks', 'library', 'prover'}:
        raise ValueError('Input must be a benchmark, library or prompt file')
    if any(p.is_symlink() for p in [path, *path.parents]) or not path.is_file():
        raise ValueError('Missing or symlinked input: ' + name)
    if not path.resolve().is_relative_to(ROOT.resolve()):
        raise ValueError('Input escaped repository')
    return path


def vernacular_sentences(text):
    """Token-aware sentence boundaries; comments and quoted notation are safe."""
    text = uncomment(text)
    start, quoted, i = 0, False, 0
    while i < len(text):
        if text[i] == '"':
            if quoted and text[i:i+2] == '""':
                i += 2
                continue
            quoted = not quoted
        if not quoted and text[i] == '.' and (i+1 == len(text) or text[i+1].isspace()):
            sentence = text[start:i+1].strip()
            if sentence:
                yield sentence
            start = i+1
        i += 1
    if quoted or text[start:].strip():
        raise ValueError('Incomplete source sentence')


def extract_interface(source):
    """Keep semantic definitions and statement headers, never proof commands.

    Some lemmas omit an explicit Proof marker. Once a lemma statement
    is seen, everything through its closing Qed/Defined is discarded.
    """
    output, proving = [], False
    for sentence in vernacular_sentences(source):
        if proving:
            if re.fullmatch(r'[}\s]*(?:Qed|Defined|Abort)\.', sentence):
                if sentence.rstrip().endswith('Abort.'):
                    output.pop()  # An aborted declaration is not an available fact.
                proving = False
            continue
        if re.match(r'(?:Lemma|Theorem|Corollary|Proposition)\b', sentence):
            output.append(sentence)
            proving = True
        elif re.match(r'(?:(?:Local|Global)\s+)?(?:Definition|Fixpoint|Inductive|Notation|'
                      r'Infix|Require|Section|End|Variable|Variables|Hypothesis|'
                      r'Hypotheses|Arguments|Open Scope|Close Scope)\b', sentence):
            output.append(sentence)
        # Ltac bodies, Check/Test/Print and opaque proof commands are excluded.
    if proving:
        raise ValueError('Unclosed helper proof')
    result = '\n\n'.join(output) + '\n'
    if PROOF_WORDS.search(result):
        raise ValueError('Proof command entered generated interface')
    return result


def generated_interface(target):
    result = '\n'.join(extract_interface(p.read_text()) for p in module_sources(target))
    if target == 'Horners':
        result += '\n' + baseline_declaration('preHorners') + '\n'
    forbidden = {target}
    if target in ('preHorners', 'Horners'):
        forbidden.add('Horners')
    if target.startswith('contour'):
        forbidden |= {'contour_row', 'contour_right', 'contour_row_pw', 'timeless_shift',
                      'timeless_unshift', 'row_col_interchange', 'interchange_2x2'}
    if target == 'monitor':
        forbidden |= {'PP_succ', 'fork_tree', 'G'}
    names = set(re.findall(r'\b(?:Lemma|Theorem|Definition|Fixpoint)\s+(\w+)', result))
    if forbidden & names:
        raise ValueError('Forbidden/equivalent named result in interface: ' + str(forbidden & names))
    return result


def audit_document(text, role):
    if PROOF_WORDS.search(text) or PROOF_LINE.search(text):
        raise ValueError('Executable proof material in ' + role)
    if role == 'paper' and (PAPER_IMPLEMENTATION.search(text) or re.search(r'```(?:coq|rocq)\b', text, re.I)):
        raise ValueError('Implementation advice in human mathematical proof')
    if role == 'interface' and re.search(r'\b(?:Axioms?|Parameters?)\b', text):
        raise ValueError('Additional trust declaration in interface')
def command(argv, directory):
    try:
        result = subprocess.run(argv, cwd=directory, capture_output=True, text=True, timeout=60)
        record = {'command': argv, 'exit_code': result.returncode,
                  'stdout': result.stdout, 'stderr': result.stderr}
    except subprocess.TimeoutExpired:
        record = {'command': argv, 'exit_code': None, 'error': 'timeout'}
    with (directory / 'commands.jsonl').open('a') as log:
        log.write(json.dumps(record) + '\n')
    return record


def assumptions(stdout):
    if 'Axioms:' not in stdout:
        return set() if 'Closed under the global context' in stdout else None
    return set(re.findall(r'^([A-Za-z_][\w.]*)\s*:', stdout.split('Axioms:')[-1], re.M))
def baseline_declaration(target):
    if target not in TARGETS:
        raise ValueError('Unknown benchmark')
    text = uncomment((SUITE / target / 'target.v').read_text())
    match = re.search(r'(Lemma\s+' + re.escape(target) + r'\s*:.*?)\bProof\s*\.', text, re.S)
    if not match:
        raise RuntimeError('Missing target declaration: ' + target)
    return match[1].strip()


def task_settings(target):
    if target not in TARGETS:
        raise ValueError('Unknown benchmark')
    return json.loads((SUITE / 'manifest.json').read_text())['tasks'][target]


def context(target):
    return task_settings(target)['context']


def module_sources(target):
    return [reviewed_path(name) for name in task_settings(target)['modules']]


def verify_inputs(target=None):
    manifest = json.loads((SUITE / 'manifest.json').read_text())
    for name, expected in manifest['sha256'].items():
        if digest(reviewed_path(name)) != expected:
            raise RuntimeError('Benchmark input changed: ' + name)
    for name in TARGETS if target is None else [target]:
        interface = (SUITE / name / 'library_interface.v').read_text()
        if interface != generated_interface(name):
            raise RuntimeError('Interface differs from library declarations: ' + name)
        for role, file in [('paper', 'paper_proof.md'), ('formalisation', 'formalisation.md'),
                           ('interface', 'library_interface.v')]:
            audit_document((SUITE / name / file).read_text(), role)
        audit_document((SUITE / 'library.md').read_text(), 'library')
        baseline_declaration(name)
    return manifest


def preHorners_prerequisite():
    raise RuntimeError('Supply --prerequisite with a complete preHorners proof from your own local run')


def bundle(target, guidance='full'):
    if guidance not in ('full', 'none'):
        raise ValueError('Unknown guidance setting')
    verify_inputs(target)
    base = SUITE / target
    sections = {'library': (SUITE / 'library.md').read_text(),
                'interface': (base / 'library_interface.v').read_text(),
                'formalisation': (base / 'formalisation.md').read_text(),
                'target': context(target) + '\n' + baseline_declaration(target),
                'paper': (base / 'paper_proof.md').read_text() if guidance == 'full' else
                         'No mathematical proof guidance is supplied in this configuration.'}
    library = ('REUSABLE ROCQ LIBRARY EXPLANATION\n' + sections['library'] +
               '\nEXACT DEFINITIONS AND PERMITTED STATEMENTS (NO PROOF BODIES)\n```coq\n' +
               sections['interface'] + '```\nBENCHMARK REPRESENTATION NOTES\n' + sections['formalisation'])
    fixed = {k: v for k, v in sections.items() if k != 'paper'}
    sections['fixed_inputs_sha256'] = hashlib.sha256(json.dumps(fixed, sort_keys=True).encode()).hexdigest()
    sections['library_summary'] = library
    sections['system'] = (SUITE / 'system.txt').read_text() + '\nPermitted tactic heads: ' + ', '.join(sorted(POLICY)) + '.'
    for phase in ('whole', 'plan'):
        template = (ROOT / 'prover/prompts' / ('prompt_whole_proof.txt' if phase == 'whole' else 'prompt_plan.txt')).read_text()
        sections[phase] = template.format(library_summary=library, theorem=sections['target'],
                                          pap_proof=sections['paper'], error_block='')
    return sections


def audit_request(system, messages, inputs):
    """Enforce the initial context of every stateless or checkpoint request.

    Later model-produced tactics and verified feedback may contain executable
    text. They are protocol history, not newly supplied reference material.
    """
    if system != inputs['system'] or not messages or messages[0] not in (
            {'role': 'user', 'content': inputs['whole']},
            {'role': 'user', 'content': inputs['plan']}):
        raise ValueError('Unreviewed initial model context')
    if any(set(m) != {'role', 'content'} or m['role'] not in {'user', 'assistant'} or
           not isinstance(m['content'], str) for m in messages):
        raise ValueError('Unsupported message source or attachment')
    return {'audited': True, 'initial_phase': 'whole' if messages[0]['content'] == inputs['whole'] else 'plan',
            'fixed_inputs_sha256': inputs['fixed_inputs_sha256'],
            'payload_sha256': hashlib.sha256(json.dumps({'system': system, 'messages': messages}, sort_keys=True).encode()).hexdigest()}


def prepare(target, out):
    verify_inputs(target)
    coqc, coqchk = shutil.which('coqc'), shutil.which('coqchk')
    if not coqc or not coqchk:
        raise RuntimeError('Put coqc and coqchk on PATH')
    for source in module_sources(target):
        clean = uncomment(source.read_text())
        if re.search(r'\b(?:Admitted|Axioms?|Parameters?)\b', clean):
            raise RuntimeError('Untrusted dependency: ' + source.name)
        shutil.copy2(source, out / source.name)
        if command([coqc, source.name], out)['exit_code'] != 0:
            raise RuntimeError('Dependency failed: ' + source.name)
    last = module_sources(target)[-1].stem
    if target == 'Horners':
        (out / 'preHorners_prerequisite.v').write_text(preHorners_prerequisite())
        result = command([coqc, 'preHorners_prerequisite.v'], out)
        if result['exit_code'] != 0 or assumptions(result['stdout']) != FOUNDATIONS:
            raise RuntimeError('Supplied prerequisite compilation/assumption failure')
        last = 'preHorners_prerequisite'
    checked_modules = [p.stem for p in module_sources(target)]
    if target == 'Horners':
        checked_modules.append(last)
    if command([coqchk, '-silent', *checked_modules], out)['exit_code'] != 0:
        raise RuntimeError('Dependency kernel replay failed')
    (out / 'initial.v').write_text((SUITE / target / 'target.v').read_text())
    inputs = bundle(target)
    (out / 'prompt_inputs.json').write_text(json.dumps(inputs, indent=2, ensure_ascii=False))
    shutil.copy2(SUITE / 'manifest.json', out / 'input_manifest.json')
    return inputs


def live_preamble(target, out):
    local = {p.stem for p in module_sources(target)} | {'preHorners_prerequisite'}
    def inline(text):
        def replace(m):
            remaining = [x for x in m[2].split() if x not in local]
            return m[1] + ' '.join(remaining) + '.' if remaining else ''
        return re.sub(r'^(\s*Require\s+(?:Import|Export)\s+)(.*?)\s*\.\s*$', replace, text, flags=re.M)
    text = '\n'.join(inline(p.read_text()) for p in module_sources(target))
    if target == 'Horners':
        text += '\n' + inline((out / 'preHorners_prerequisite.v').read_text().split('Print Assumptions')[0])
    return text + '\n' + inline(context(target))


def validate(target, candidate, out, label='checked'):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', label):
        raise ValueError('Invalid module name')
    normalized, reason = screen(candidate, baseline_declaration(target), allowed_tactics=POLICY)
    result = {'accepted': False, 'reason': reason}
    if normalized is None:
        return result
    ending = '\nEnd Task.\n' if target == 'monitor' else '\n'
    (out / (label + '.v')).write_text(context(target) + '\n' + normalized + ending +
                                     'Print Assumptions ' + target + '.\n')
    result['compiler'] = command([shutil.which('coqc'), label + '.v'], out)
    if result['compiler']['exit_code'] != 0:
        result['reason'] = 'compiler_rejected'
        return result
    actual = assumptions(result['compiler']['stdout'])
    result['assumptions'] = sorted(actual) if actual is not None else None
    if actual != FOUNDATIONS:
        result['reason'] = 'unexpected_assumptions'
        return result
    result['kernel_replay'] = command([shutil.which('coqchk'), '-silent', label], out)
    result['accepted'] = result['kernel_replay']['exit_code'] == 0
    result['reason'] = 'accepted' if result['accepted'] else 'kernel_rejected'
    return result
