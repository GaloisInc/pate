#!/usr/bin/env python3
#
# This tool takes as arguments a list of zip files where each contains an Anvill
# JSON file; it combines all of the Anvill JSON files into a single monolithic
# file with multiple function entries.
#
# Anvill is a tool developed by Trail of Bits that lifts binaries to LLVM
# bitcode; it is driven by a JSON file as input that provides details about
# arguments and stack layout.

import argparse
import json
import pathlib
import zipfile

def main(args):
    # Start with a missing JSON object; we'll save the first one to get the
    # outer structure in place and, from there, start adding functions as they
    # are discovered in future zip files
    combined = None
    for zipPath in args.paths:
        with zipfile.ZipFile(zipPath) as archive:
            for compressedFileName in archive.namelist():
                p = pathlib.PurePath(compressedFileName)
                if not p.suffix == ".json":
                    continue
                with archive.open(compressedFileName) as jsonFile:
                    obj = json.load(jsonFile)
                    if combined is None:
                        combined = obj
                        if not 'variables' in combined:
                            combined['variables'] = []
                        if not 'symbols' in combined:
                            combined['symbols'] = []
                    else:
                        if combined['arch'] == obj['arch'] and combined['os'] == obj['os']:
                            combined['functions'].extend(obj['functions'])
                            combined['variables'].extend(obj['variables'])
                            combined['symbols'].extend(obj['symbols'])
    if not combined is None:
        # We don't need the memory specification. It can be fairly large, so
        # just delete it.
        del combined['memory']
        with open(args.output, 'w') as out:
            json.dump(combined, out, indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Combine Anvill JSON files')
    parser.add_argument('paths', metavar='ZIPFILE', type=str, nargs='+',
                        help='A zip file containing an Anvill JSON file')
    parser.add_argument('--output', metavar='FILE', dest='output', action='store',
                        help='The combined JSON file to produce')


    args = parser.parse_args()
    main(args)
