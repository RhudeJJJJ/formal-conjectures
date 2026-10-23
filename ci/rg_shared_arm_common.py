from fractions import Fraction as Q

def rational(value):
    value=Q(value)
    return str(value.numerator) if value.denominator==1 else f'({value.numerator}/{value.denominator})'

def module(namespace,imports,body):
    return ('/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n'
        + ''.join('import '+name+'\n' for name in imports)
        + f'namespace Gebendorfer.RadenkovicGutman.{namespace}\n'
        + 'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
        + body + f'end Gebendorfer.RadenkovicGutman.{namespace}\n')
