"""Tactic parsing, focus controls and checkpoint continuation."""
import re
from types import FunctionType, SimpleNamespace
from guided_inputs import uncomment

IntegrityError = RuntimeError
SearchLimit = ValueError

def structural_action(text):
    return text in ('{', '}') or bool(re.fullmatch(r'-+|\++|\*+|[1-9][0-9]*\s*:\s*\{', text))

def sentences(code):
    clean = uncomment(code)
    result, start, quoted, i = [], 0, False, 0
    while i < len(clean):
        c = clean[i]
        if c == '"':
            if quoted and i + 1 < len(clean) and clean[i + 1] == '"':
                i += 2
                continue
            quoted = not quoted
        if not quoted:
            if not clean[start:i].strip():
                focus = re.match(r'[1-9][0-9]*\s*:\s*\{', clean[i:])
                if focus:
                    end = i + len(focus[0])
                    result.append(clean[i:end])
                    start = end
                    i = end
                    continue
                if c in '{}':
                    result.append(c)
                    start = i + 1
                elif c in '-+*':
                    end = i + 1
                    while end < len(clean) and clean[end] == c:
                        end += 1
                    if end == len(clean) or clean[end].isspace():
                        result.append(clean[i:end])
                        start = end
                        i = end
                        continue
            if c == '.' and (i + 1 == len(clean) or clean[i + 1].isspace()):
                item = clean[start:i + 1].strip()
                if item and item not in ('Proof.', 'Qed.'):
                    result.append(item)
                start = i + 1
        i += 1
    if quoted or clean[start:].strip():
        raise ValueError('Incomplete tactic sentence or string')
    return result
def extract_tactics(raw):
    blocks = re.findall(r'```(?:coq|rocq)?\s*\n(.*?)```', raw, re.S)
    if '```' in raw:
        if len(blocks) != 1 or raw.count('```') != 2:
            return []
        raw = blocks[0]
    try:
        return sentences(raw.strip())
    except ValueError:
        return []


def replay(coq, tactics):
    applied = []
    for tactic in tactics:
        tactic = tactic.strip()
        # Normalize reverse series-rewrite notation.
        tactic = re.sub(r'^(series_rewrite(?:_lhs|_rhs)?)\s+<-\s+',
                        lambda match: match.group(1) + '_rev ', tactic)
        if not tactic:
            continue
        if not structural_action(tactic) and not tactic.endswith('.'):
            tactic += '.'
        accepted, error = coq.try_tactic(tactic)
        if not accepted:
            return applied, f'Tactic `{tactic}` failed: {error}'
        applied.append(tactic)
    return applied, None
def validation_inputs(g):
    """Validate proof actions with numeric focus and kernel checking.

    Screen a copy with focus indices removed, then compile the submitted proof
    with its indices intact. No tactic or vernacular vocabulary is expanded.
    """
    def screen(candidate,declaration,*,allowed_tactics):
        try:clean=g.uncomment(candidate).strip()
        except ValueError:return None,'malformed_comment'
        match=re.fullmatch(r'(Lemma\s+\w+\s*:.*?)\bProof\s*\.(.*?)\bQed\s*\.',clean,re.S)
        if not match:return g.screen(candidate,declaration,allowed_tactics=allowed_tactics)
        try:actions=sentences(match[2])
        except ValueError:return None,'incomplete_tactic_sentence'
        sanitized='\n'.join('{' if structural_action(a) and ':' in a else a for a in actions)
        # Terminate the screening copy with a tactic after any closing focus.
        checked=match[1]+'Proof.\n'+sanitized+'\nreflexivity.\nQed.'
        normalized,reason=g.screen(checked,declaration,allowed_tactics=allowed_tactics)
        if reason:return None,reason
        return declaration+'\nProof.\n'+match[2]+'\nQed.\n',None
    globals_=dict(g.__dict__,screen=screen)
    validate=FunctionType(g.validate.__code__,globals_,argdefs=g.validate.__defaults__,closure=g.validate.__closure__)
    return SimpleNamespace(**dict(g.__dict__,screen=screen,validate=validate))


def parse_plan(raw,parser):
    headers=list(re.finditer(r'(?m)^\s*SEGMENT\s+([^\n:]+)\s*:\s*',raw))
    if not headers:raise SearchLimit('Malformed checkpoint plan: no labeled blocks')
    chunks=[]
    for i,h in enumerate(headers):
        body=raw[h.end():headers[i+1].start() if i+1<len(headers) else len(raw)]
        chunks.append(f'SEGMENT seg_{i+1:02d}:\n'+body.strip())
    result=parser('\n'.join(chunks))
    if len(result)!=len(headers) or any(not s['pap_excerpt'] or not s['target'] for s in result):
        raise SearchLimit('Malformed checkpoint plan: missing pap/after fields')
    for item,h in zip(result,headers):item['original_label']=h[1].strip()
    return result
