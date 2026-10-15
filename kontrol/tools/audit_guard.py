#!/usr/bin/env python3
"""Sequential full guard graph audit in the one-worker envelope."""
import sys
import audit


def main():
    for name in ['threshold0', 'threshold0correct', 'guard4', 'literal4', 'guard36', 'naturalposts', 'negative']:
        sys.argv=[sys.argv[0],name]
        audit.main()


if __name__=='__main__':
    main()
