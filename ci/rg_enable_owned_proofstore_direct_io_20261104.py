"""Enable backing-file direct I/O only on this job's new, empty proofstore.

The original setup, filesystem, restore checks and resource guards are unchanged.
The sole device mutation is LOOP_SET_DIRECT_IO on the already mounted owned loop.
This diagnostic storage observation is not a Lean receipt or a proof export.
"""
import hashlib
import json
import os
import pathlib
import re
import stat
import subprocess
import sys


REPORT_NAME = 'rg-proofstore-direct-io.json'
LOOP_COLUMNS = 'NAME,BACK-FILE,BACK-INO,BACK-MAJ:MIN,OFFSET,SIZELIMIT,RO,DIO,LOG-SEC,MAJ:MIN,AUTOCLEAR'
MOUNT_COLUMNS = 'SOURCE,TARGET,FSTYPE,OPTIONS,MAJ:MIN'
LOOP_IMMUTABLE = ('name', 'back-file', 'back-ino', 'back-maj:min', 'offset',
                  'sizelimit', 'ro', 'log-sec', 'maj:min', 'autoclear')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def device_number(value):
    return f'{os.major(value)}:{os.minor(value)}'


def integer(value, minimum=0):
    return type(value) is int and value >= minimum


def image_identity(value):
    require(stat.S_ISREG(value.st_mode), 'owned image is not a regular file')
    return {'device': device_number(value.st_dev), 'inode': value.st_ino,
            'size': value.st_size}


def capture(argv, report, check=True):
    result = subprocess.run(argv, capture_output=True, text=True, timeout=60,
                            env={**os.environ, 'LC_ALL': 'C'})
    report['commands'].append({'argv': argv, 'returncode': result.returncode,
                               'stdout': result.stdout, 'stderr': result.stderr})
    if check:
        require(result.returncode == 0, 'command failed: ' + ' '.join(argv))
    return result.stdout


def single_row(payload, key):
    rows = payload.get(key)
    require(isinstance(rows, list) and len(rows) == 1 and isinstance(rows[0], dict),
            'expected exactly one ' + key + ' row')
    require(not rows[0].get('children'), 'unexpected child devices or mounts')
    return rows[0]


def validate_mount(row, setup, mount):
    require(row.get('target') == str(mount), 'target is not the exact proofstore mount')
    require(row.get('fstype') == 'btrfs', 'proofstore is not btrfs')
    require(re.fullmatch(r'/dev/loop[0-9]+', row.get('source', '')) is not None,
            'proofstore source is not one whole loop device')
    options = row.get('options', '').split(',')
    require('rw' in options and 'ro' not in options and 'compress=zstd:6' in options,
            'proofstore mount options changed')
    for key in ('source', 'target', 'fstype'):
        require(row.get(key) == setup['filesystem'].get(key), 'setup mount identity changed: ' + key)
    require(set(options) == set(setup['filesystem']['options'].split(',')),
            'setup mount options changed')
    require(re.fullmatch(r'[0-9]+:[0-9]+', row.get('maj:min', '')) is not None,
            'mount device number is unavailable')


def validate_loop(row, image, identity, loop, loop_number):
    require(row.get('name') == loop and row.get('maj:min') == loop_number,
            'losetup returned a different loop device')
    require(row.get('back-file') == str(image), 'loop backing pathname differs')
    require(integer(row.get('back-ino'), 1) and row['back-ino'] == identity['inode'],
            'loop backing inode differs')
    require(row.get('back-maj:min') == identity['device'], 'loop backing device differs')
    require(type(row.get('offset')) is int and row['offset'] == 0, 'nonzero or missing loop offset')
    require(type(row.get('sizelimit')) is int and row['sizelimit'] == 0,
            'nonzero or missing loop size limit')
    require(row.get('ro') is False, 'loop is not confirmed read/write')
    require(type(row.get('dio')) is bool and type(row.get('autoclear')) is bool,
            'effective loop flags are unavailable')
    require(integer(row.get('log-sec'), 1), 'loop logical sector size is unavailable')


def backing_block_info(identity):
    """Read the backing device's logical sector size, including partition parents."""
    node = pathlib.Path('/sys/dev/block') / identity['device']
    result = {'image_device': identity['device'], 'sysfs': str(node)}
    if not node.exists():
        return {**result, 'status': 'NO_SYSFS_BLOCK_DEVICE_FOR_IMAGE_ST_DEV',
                'logical_sector_bytes': None}
    real = node.resolve(strict=True)
    queue = real / 'queue/logical_block_size'
    if not queue.is_file() and (real / 'partition').is_file():
        queue = real.parent / 'queue/logical_block_size'
    if not queue.is_file():
        return {**result, 'status': 'LOGICAL_SECTOR_SIZE_NOT_EXPOSED',
                'resolved_sysfs': str(real), 'logical_sector_bytes': None}
    size = int(queue.read_text().strip())
    require(size > 0, 'invalid backing logical sector size')
    return {**result, 'status': 'READ_FROM_SYSFS', 'resolved_sysfs': str(real),
            'logical_sector_source': str(queue), 'logical_sector_bytes': size}


def validate_sector_compatibility(row, backing):
    size = backing['logical_sector_bytes']
    if size is not None:
        require(integer(size, 1), 'invalid backing logical sector size')
        require(row['log-sec'] >= size and row['offset'] % size == 0,
                'loop sector size/offset is incompatible with backing block device direct I/O')


def observe(workspace, image, image_fd, identity, mount, setup, report):
    require(image.resolve(strict=True) == image and not image.is_symlink(), 'image path changed')
    require(image_identity(image.lstat()) == identity, 'owned image identity changed')
    require(image_identity(os.fstat(image_fd)) == identity, 'opened image identity changed')
    require(mount.resolve(strict=True) == mount and not mount.is_symlink(), 'mount path changed')
    require(not any(mount.iterdir()), 'proofstore is not empty before its first restore')
    row = single_row(json.loads(capture(['findmnt', '--json', '--target', str(mount),
                                        '--output', MOUNT_COLUMNS], report)), 'filesystems')
    validate_mount(row, setup, mount)
    # Btrfs mountinfo sb->s_dev, stat root->anon_dev and block-device rdev
    # are separate identities. Record each; do not assert false equalities.
    mount_stat_device = device_number(mount.stat().st_dev)
    loop = row['source']
    loop_path = pathlib.Path(loop)
    require(not loop_path.is_symlink(), 'loop device pathname is a symlink')
    loop_stat = loop_path.stat()
    require(stat.S_ISBLK(loop_stat.st_mode), 'loop pathname is not a block device')
    loop_number = device_number(loop_stat.st_rdev)
    require(os.major(loop_stat.st_rdev) == 7, 'source is not a loop block device')
    loop_row = single_row(json.loads(capture(['sudo', '-n', '--', 'losetup', '--list',
                                             '--json', '--output', LOOP_COLUMNS, '--', loop], report)),
                          'loopdevices')
    validate_loop(loop_row, image, identity, loop, loop_number)
    sysfs = pathlib.Path('/sys/dev/block') / loop_number
    require(sysfs.resolve(strict=True).name == loop_path.name, 'loop sysfs identity differs')
    dio_text = (sysfs / 'loop/dio').read_text().strip()
    require(dio_text in ('0', '1') and (dio_text == '1') == loop_row['dio'],
            f'effective DIO readbacks disagree: losetup={loop_row["dio"]!r}, sysfs={dio_text!r}')
    loop_sector = int((sysfs / 'queue/logical_block_size').read_text().strip())
    require(loop_sector == loop_row['log-sec'], 'loop logical sector readbacks disagree')
    backing = backing_block_info(identity)
    validate_sector_compatibility(loop_row, backing)
    outer = single_row(json.loads(capture(['findmnt', '--json', '--target', str(image),
                                          '--output', MOUNT_COLUMNS], report)), 'filesystems')
    require(re.fullmatch(r'[0-9]+:[0-9]+', outer.get('maj:min', '')) is not None,
            'outer mount filesystem device number is unavailable')
    require(image.is_relative_to(pathlib.Path(outer['target'])), 'outer mount does not contain image')
    return {'image_identity': identity, 'mount': row, 'mount_stat_device': mount_stat_device,
            'loop': loop_row,
            'sysfs_dio': int(dio_text), 'backing_block': backing, 'backing_filesystem': outer}


def main():
    require(len(sys.argv) == 1, 'this fixed helper accepts no device or path arguments')
    require(os.environ.get('GITHUB_ACTIONS') == 'true', 'not a GitHub Actions job')
    require(os.environ.get('RUNNER_ENVIRONMENT') == 'github-hosted'
            and os.environ.get('RUNNER_OS') == 'Linux', 'not a fresh GitHub-hosted Linux runner')
    require(os.environ.get('GITHUB_REPOSITORY') == 'RhudeJJJJ/formal-conjectures'
            and os.environ.get('GITHUB_REF') == 'refs/heads/rg-d1-bothlong-phase-probe-20261104',
            'not the fixed diagnostic branch')
    workspace = pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve(strict=True)
    require(workspace.is_relative_to('/home/runner/work'), 'unexpected hosted workspace')
    image = workspace / 'rg-ephemeral-proofstore.btrfs'
    mount = workspace / 'Proofs/RG_Lean_20261019/build/extension'
    report_path = workspace / REPORT_NAME
    require(not report_path.exists() and not report_path.is_symlink(), 'DIO report already exists')
    report = {'status': 'OWNED_PROOFSTORE_LOOP_DIRECT_IO_REJECTED',
              'native_run_id': os.environ.get('GITHUB_RUN_ID'),
              'native_run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
              'native_workflow_source_commit': os.environ.get('GITHUB_SHA'),
              'image': str(image), 'mount': str(mount), 'commands': [],
              'proof_export_claim': False, 'resource_limits_changed': False,
              'filesystem_recreated_or_remounted': False, 'swap_configuration_changed': False}
    try:
        setup_path = workspace / 'rg-proofstore-setup.json'
        require(setup_path.is_file() and not setup_path.is_symlink(), 'setup report is unavailable')
        setup_bytes = setup_path.read_bytes()
        report['setup_report_sha256'] = hashlib.sha256(setup_bytes).hexdigest()
        setup = json.loads(setup_bytes)
        require(setup.get('status') == 'NEW_EPHEMERAL_COMPRESSED_PROOFSTORE_MOUNTED',
                'original fresh proofstore setup did not succeed')
        require(setup.get('image') == str(image) and setup.get('mount') == str(mount),
                'setup report names another image or mount')
        require(setup.get('logical_image_bytes') == 256 * 1024**3, 'unexpected logical proofstore size')
        require(image.resolve(strict=True) == image and not image.is_symlink(), 'image is not the owned path')
        with os.fdopen(os.open(image, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as image_stream:
            identity = image_identity(os.fstat(image_stream.fileno()))
            require(identity['size'] == setup['logical_image_bytes'], 'image size differs from setup')
            report['kernel_release'] = capture(['uname', '--release'], report).strip()
            report['util_linux_version'] = capture(['losetup', '--version'], report).strip()
            before = observe(workspace, image, image_stream.fileno(), identity, mount, setup, report)
            report['before'] = before
            print(json.dumps({'phase': 'before', 'loop': before['loop'],
                              'sysfs_dio': before['sysfs_dio'], 'backing_block': before['backing_block']}), flush=True)
            # The only device mutation. No create, detach, resize, remount or fallback.
            capture(['sudo', '-n', '--', 'losetup', '--direct-io=on', '--', before['loop']['name']],
                    report, check=False)
            toggle_returncode = report['commands'][-1]['returncode']
            after = observe(workspace, image, image_stream.fileno(), identity, mount, setup, report)
            report['after'] = after
            print(json.dumps({'phase': 'after', 'loop': after['loop'],
                              'sysfs_dio': after['sysfs_dio']}), flush=True)
            require(toggle_returncode == 0, 'owned-loop DIO ioctl failed; no fallback attempted')
            require(all(before['loop'][key] == after['loop'][key] for key in LOOP_IMMUTABLE),
                    'a loop property other than DIO changed')
            require(before['mount'] == after['mount']
                    and before['mount_stat_device'] == after['mount_stat_device']
                    and before['backing_block'] == after['backing_block']
                    and before['backing_filesystem'] == after['backing_filesystem'],
                    'mount or backing device observations changed')
            require(after['loop']['dio'] is True and after['sysfs_dio'] == 1,
                    'effective direct I/O is not enabled')
            report['dio_flag_changed'] = before['loop']['dio'] is False
            report['status'] = 'OWNED_PROOFSTORE_LOOP_DIRECT_IO_ENABLED'
    except Exception as error:
        report['error'] = f'{type(error).__name__}: {error}'
        raise
    finally:
        # Always retain actual observations, including a rejected activation.
        with report_path.open('x') as stream:
            json.dump(report, stream, indent=2, sort_keys=True)
            stream.write('\n')


if __name__ == '__main__':
    main()
