"""Pure post-cleanup acceptance; never discover, signal, wait for or adopt a PID."""


def require_known_joins(document):
    """Collection completeness does not authenticate an unknown joined child."""
    def need(condition, message):
        if not condition:
            raise RuntimeError(message)

    need(isinstance(document, dict), 'observation document type')
    need(document.get('schema') == 'oak-owned-process-observation-v1' and
         document.get('complete') is True and document.get('overflow') is False and
         document.get('errors') == [], 'observation collection incomplete')
    events = document.get('events')
    need(isinstance(events, list) and len(events) <= 128, 'observation event list')
    for event in events:
        need(isinstance(event, dict) and event.get('kind') in
             ('spawn', 'join', 'cleanup-result'), 'observation event type')
        if event['kind'] != 'join':
            continue
        pid = event.get('pid')
        identity = event.get('observed_identity')
        need(type(pid) is int and pid > 0 and isinstance(identity, list) and
             len(identity) == 2 and all(type(value) is int and value > 0 for value in identity) and
             identity[0] == pid, 'unknown or malformed joined identity')
        # Historical candidates never supply the current observed identity.
        basis = event.get('identity_basis')
        raw = event.get('raw_wait4_status')
        need(type(event.get('decoded_status')) is int, 'missing decoded join status')
        if basis == 'current direct-child observation before wait4':
            need(type(raw) is int and raw >= 0, 'missing raw wait4 status')
        elif basis == 'observed direct Popen spawn':
            need('raw_wait4_status' in event and raw is None, 'Popen join must be decoded-only')
        else:
            need(False, 'unsupported joined identity basis')


def check_acceptance_controls():
    """Finite in-memory controls, charged within the invoking gate allocation."""
    def document(events):
        return {'schema': 'oak-owned-process-observation-v1', 'complete': True,
                'overflow': False, 'errors': [], 'events': events}

    raw = {'kind': 'join', 'pid': 17, 'observed_identity': [17, 101],
           'raw_wait4_status': 0, 'decoded_status': 0,
           'identity_basis': 'current direct-child observation before wait4',
           'historical_candidates': []}
    decoded = dict(raw, raw_wait4_status=None, identity_basis='observed direct Popen spawn')
    missing_identity = dict(raw)
    missing_identity.pop('observed_identity')
    cases = [
        ('empty-join-set', document([]), True),
        ('known-current-raw', document([raw]), True),
        ('known-spawn-decoded', document([decoded]), True),
        ('unknown-with-history', document([dict(raw, observed_identity=None,
                                               historical_candidates=[[17, 101]])]), False),
        ('missing-identity', document([missing_identity]), False),
        ('scalar-identity', document([dict(raw, observed_identity=101)]), False),
        ('mismatched-pid', document([dict(raw, observed_identity=[18, 101])]), False),
        ('nonpositive-start', document([dict(raw, observed_identity=[17, 0])]), False),
        ('boolean-pid', document([dict(raw, pid=True, observed_identity=[True, 101])]), False),
        ('historical-basis', document([dict(raw, identity_basis='historical candidate')]), False),
        ('missing-raw-status', document([dict(raw, raw_wait4_status=None)]), False),
        ('fabricated-popen-raw', document([dict(decoded, raw_wait4_status=0)]), False),
        ('malformed-events', document(None), False),
        ('incomplete-collection', dict(document([raw]), complete=False), False),
    ]
    results = []
    for name, value, expected in cases:
        try:
            require_known_joins(value)
            accepted = True
        except RuntimeError:
            accepted = False
        if accepted != expected:
            raise RuntimeError('observation acceptance control failed: ' + name)
        results.append({'name': name, 'accepted': accepted})
    return {'schema': 'oak-owned-observation-acceptance-control-v1',
            'cases': len(results), 'all_expected': True, 'results': results}
