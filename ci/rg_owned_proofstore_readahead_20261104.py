"""One owned Btrfs filesystem's readahead experiment; no proof or limit changes.

Enable runs after the unchanged DIO gate and before the first restore. Check is
read-only after preflight. Only the identified filesystem BDI read_ahead_kb may
be written, once, from a measured positive value to zero. Neither the loop's
queue nor its backing device is changed. Compression may still read an entire
compressed extent; zero readahead is not a promise of zero speculative I/O.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import stat
import subprocess

import rg_enable_owned_proofstore_direct_io_20261104 as dio


DIO_HELPER_SHA256 = '96211dac3452504564d33b7e2d90bdbc59597fa07eb953fc26fc6e4a56add5af'
SETUP_NAME = 'rg-proofstore-setup.json'
ENABLE_NAME = 'rg-proofstore-readahead-enable.json'
CHECK_NAME = 'rg-proofstore-readahead-check.json'
UUID_PATTERN = r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}'
NATIVE_KEYS = ('native_run_id', 'native_run_attempt', 'native_workflow_source_commit')
IDENTITY_KEYS = ('image_identity', 'mount', 'mount_stat_device', 'loop',
                 'sysfs_dio', 'backing_block', 'backing_filesystem',
                 'filesystem_uuid', 'filesystem_sysfs', 'filesystem_sysfs_identity',
                 'filesystem_device_links', 'bdi_link', 'resolved_bdi',
                 'resolved_bdi_identity', 'readahead_file')
require = dio.require


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    require(path.resolve(strict=True) == path and not path.is_symlink(),
            'report is not the exact regular path: ' + str(path))
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), 'report is not a regular file')
        raw = stream.read()
    value = json.loads(raw)
    require(isinstance(value, dict), 'report is not a JSON object')
    return value, sha256(raw)


def sysfs_identity(path):
    value = path.stat()
    return {'device': dio.device_number(value.st_dev), 'inode': value.st_ino}


def unsigned_value(text):
    require(isinstance(text, str) and re.fullmatch(r'[0-9]+\n?', text) is not None,
            'missing or invalid unsigned sysfs value')
    return int(text.strip())


def read_readahead(path):
    real = path.resolve(strict=True)
    require(not path.is_symlink() and stat.S_ISREG(real.stat().st_mode),
            'readahead attribute is not a regular sysfs attribute')
    require(real.is_relative_to('/sys/devices'), 'readahead resolved outside device sysfs')
    return {'path': str(path), 'resolved_path': str(real),
            'identity': sysfs_identity(real), 'value_kib': unsigned_value(path.read_text())}


def parse_blkid(text):
    result = {}
    for line in text.splitlines():
        if not line:
            continue
        require('=' in line, 'invalid blkid export line')
        key, value = line.split('=', 1)
        require(re.fullmatch(r'[A-Z0-9_]+', key) is not None and key not in result,
                'invalid or duplicate blkid field')
        result[key] = value
    require(result.get('TYPE') == 'btrfs', 'blkid does not confirm Btrfs')
    require(re.fullmatch(UUID_PATTERN, result.get('UUID', '')) is not None,
            'blkid filesystem UUID is unavailable or not canonical')
    return result


def select_owned_loop(payload, image_identity):
    rows = payload.get('loopdevices')
    require(isinstance(rows, list) and all(isinstance(row, dict) for row in rows),
            'loop inventory is unavailable')
    owned = [row for row in rows
             if row.get('back-maj:min') == image_identity['device']
             and row.get('back-ino') == image_identity['inode']]
    require(len(owned) == 1, 'image is not backed by exactly one live loop device')
    require(not owned[0].get('children'), 'owned loop has child devices')
    return owned[0]


def validate_sysfs_binding(uuid, blkid, loop_name, loop_number, loop_sysfs,
                           filesystem_sysfs, device_links, bdi_link, resolved_bdi):
    require(re.fullmatch(r'/dev/loop[0-9]+', loop_name) is not None
            and re.fullmatch(r'7:[0-9]+', loop_number) is not None,
            'not one whole loop block-device identity')
    require(re.fullmatch(UUID_PATTERN, uuid or '') is not None
            and blkid.get('UUID') == uuid and blkid.get('TYPE') == 'btrfs',
            'findmnt and direct blkid filesystem identities disagree')
    require(filesystem_sysfs == '/sys/fs/btrfs/' + uuid, 'wrong filesystem sysfs directory')
    require(loop_sysfs == '/sys/devices/virtual/block/' + pathlib.Path(loop_name).name,
            'loop sysfs resolved to another block device')
    expected = [{'name': pathlib.Path(loop_name).name,
                 'resolved_path': loop_sysfs, 'device_number': loop_number}]
    require(device_links == expected, 'Btrfs does not have exactly the one owned loop device')
    require(bdi_link == filesystem_sysfs + '/bdi', 'BDI link is not the owned filesystem link')
    require(re.fullmatch(r'/sys/devices/virtual/bdi/btrfs-[0-9]+', resolved_bdi) is not None,
            'filesystem BDI does not resolve to one Btrfs-owned virtual BDI')


def validate_inputs(setup, setup_sha, dio_report, context, image, mount):
    require(setup.get('status') == 'NEW_EPHEMERAL_COMPRESSED_PROOFSTORE_MOUNTED'
            and setup.get('image') == str(image) and setup.get('mount') == str(mount)
            and setup.get('logical_image_bytes') == 256 * 1024**3,
            'original setup report does not bind the new fixed proofstore')
    require(dio_report.get('status') == 'OWNED_PROOFSTORE_LOOP_DIRECT_IO_ENABLED'
            and dio_report.get('setup_report_sha256') == setup_sha
            and dio_report.get('image') == str(image) and dio_report.get('mount') == str(mount),
            'successful original DIO report does not bind this setup')
    require(all(dio_report.get(key) == context[key] for key in NATIVE_KEYS),
            'DIO report belongs to another native run, attempt or workflow head')
    require(dio_report['after']['loop']['dio'] is True
            and type(dio_report['after']['sysfs_dio']) is int
            and dio_report['after']['sysfs_dio'] == 1, 'DIO report lacks effective DIO')


def validate_transition(before, after):
    require(all(before[key] == after[key] for key in IDENTITY_KEYS),
            'proofstore identity or DIO changed during readahead observation')
    require(before['other_device_readahead'] == after['other_device_readahead'],
            'loop or backing-device readahead changed')
    require(type(before['read_ahead_kib']) is int and before['read_ahead_kib'] > 0,
            'preexisting zero or unknown readahead is not a new bounded experiment')
    require(type(after['read_ahead_kib']) is int and after['read_ahead_kib'] == 0,
            'owned filesystem readahead did not read back as zero')
    require(before['mount_empty'] is True and after['mount_empty'] is True,
            'enable must finish before the first restore')


def validate_enable_report(enabled, binding, current):
    require(enabled.get('status') == 'OWNED_PROOFSTORE_READAHEAD_ZERO_ENABLED',
            'the original readahead enable gate did not succeed')
    require(enabled.get('phase') == 'enable' and enabled.get('binding') == binding,
            'enable report has a different run/head/helper/setup/DIO binding')
    validate_transition(enabled['before'], enabled['after'])
    expected_argv = ['sudo', '-n', '--', 'tee', '--', enabled['before']['readahead_file']['path']]
    require(enabled.get('mutation') == {'argv': expected_argv, 'input': '0\n', 'returncode': 0,
                                        'stdout': '0\n', 'stderr': ''},
            'enable report lacks the one exact successful filesystem-only write')
    require(all(current[key] == enabled['after'][key] for key in IDENTITY_KEYS),
            'proofstore immutable identity changed after enable')
    require(current['other_device_readahead'] == enabled['after']['other_device_readahead'],
            'loop or backing-device readahead changed after enable')
    require(type(current['read_ahead_kib']) is int and current['read_ahead_kib'] == 0,
            'filesystem readahead is no longer zero; no reset is permitted')


def observe(workspace, image, image_fd, identity, mount, setup, dio_report, report, require_empty):
    require(image.resolve(strict=True) == image and not image.is_symlink(), 'image path changed')
    require(dio.image_identity(image.lstat()) == identity
            and dio.image_identity(os.fstat(image_fd)) == identity, 'owned image identity changed')
    require(identity == dio_report['after']['image_identity'], 'image differs from actual DIO setup')
    require(mount.resolve(strict=True) == mount and not mount.is_symlink(), 'mount path changed')
    empty = not any(mount.iterdir())
    require(not require_empty or empty, 'proofstore is not empty before its first restore')
    row = dio.single_row(json.loads(dio.capture(
        ['sudo', '-n', '--', 'findmnt', '--json', '--target', str(mount),
         '--output', dio.MOUNT_COLUMNS + ',UUID'], report)), 'filesystems')
    dio.validate_mount(row, setup, mount)
    mount_row = {key.lower(): row[key.lower()] for key in dio.MOUNT_COLUMNS.split(',')}
    mount_device = dio.device_number(mount.stat().st_dev)
    require(mount_row == dio_report['after']['mount']
            and mount_device == dio_report['after']['mount_stat_device'],
            'mount identity differs from DIO setup; Btrfs and loop IDs stay distinct')
    loop_name = row['source']
    loop_path = pathlib.Path(loop_name)
    require(not loop_path.is_symlink(), 'loop device pathname is a symlink')
    loop_stat = loop_path.stat()
    require(stat.S_ISBLK(loop_stat.st_mode) and os.major(loop_stat.st_rdev) == 7,
            'source is not a whole loop block device')
    loop_number = dio.device_number(loop_stat.st_rdev)
    loop_row = select_owned_loop(json.loads(dio.capture(
        ['sudo', '-n', '--', 'losetup', '--list', '--json', '--output', dio.LOOP_COLUMNS], report)), identity)
    dio.validate_loop(loop_row, image, identity, loop_name, loop_number)
    require(loop_row == dio_report['after']['loop'] and loop_row['dio'] is True,
            'live loop identity or DIO differs from original successful DIO gate')
    loop_sysfs = (pathlib.Path('/sys/dev/block') / loop_number).resolve(strict=True)
    require((loop_sysfs / 'dev').read_text().strip() == loop_number, 'loop sysfs dev differs')
    sysfs_dio = unsigned_value((loop_sysfs / 'loop/dio').read_text())
    require(sysfs_dio == 1, 'effective loop DIO is not one')
    require(unsigned_value((loop_sysfs / 'queue/logical_block_size').read_text()) == loop_row['log-sec'],
            'loop logical sector readbacks differ')
    backing = dio.backing_block_info(identity)
    dio.validate_sector_compatibility(loop_row, backing)
    require(backing == dio_report['after']['backing_block']
            and backing['status'] == 'READ_FROM_SYSFS', 'backing block identity/geometry unavailable or changed')
    outer = dio.single_row(json.loads(dio.capture(
        ['findmnt', '--json', '--target', str(image), '--output', dio.MOUNT_COLUMNS], report)), 'filesystems')
    require(outer == dio_report['after']['backing_filesystem'], 'backing filesystem changed')
    blkid = parse_blkid(dio.capture(
        ['sudo', '-n', '--', 'blkid', '--probe', '--output', 'export', '--', loop_name], report))
    uuid = row.get('uuid')
    require(re.fullmatch(UUID_PATTERN, uuid or '') is not None, 'findmnt UUID unavailable')
    fs_path = pathlib.Path('/sys/fs/btrfs') / uuid
    require(fs_path.resolve(strict=True) == fs_path and fs_path.is_dir(), 'unexpected Btrfs sysfs path')
    devices_path = fs_path / 'devices'
    require(devices_path.resolve(strict=True) == devices_path and devices_path.is_dir(),
            'unexpected Btrfs devices directory')
    links = []
    for device in sorted(devices_path.iterdir()):
        require(device.is_symlink(), 'filesystem device entry is not a symlink')
        real = device.resolve(strict=True)
        links.append({'name': device.name, 'resolved_path': str(real),
                      'device_number': (real / 'dev').read_text().strip()})
    bdi_link = fs_path / 'bdi'
    require(bdi_link.is_symlink(), 'filesystem BDI link is unavailable')
    bdi = bdi_link.resolve(strict=True)
    validate_sysfs_binding(uuid, blkid, loop_name, loop_number, str(loop_sysfs),
                           str(fs_path), links, str(bdi_link), str(bdi))
    ra = read_readahead(bdi_link / 'read_ahead_kb')
    require(ra['resolved_path'] == str(bdi / 'read_ahead_kb'), 'readahead escaped the owned BDI')
    other = {
        'loop_queue': read_readahead(loop_sysfs / 'queue/read_ahead_kb'),
        'backing_queue': read_readahead(pathlib.Path(backing['logical_sector_source']).parent / 'read_ahead_kb'),
    }
    require(all(value['resolved_path'] != ra['resolved_path'] for value in other.values()),
            'filesystem BDI aliases another device readahead attribute')
    return {'image_identity': identity, 'mount': mount_row, 'mount_stat_device': mount_device,
            'loop': loop_row, 'sysfs_dio': sysfs_dio, 'backing_block': backing,
            'backing_filesystem': outer, 'filesystem_uuid': uuid,
            'filesystem_sysfs': str(fs_path), 'filesystem_sysfs_identity': sysfs_identity(fs_path),
            'filesystem_device_links': links, 'bdi_link': str(bdi_link), 'resolved_bdi': str(bdi),
            'resolved_bdi_identity': sysfs_identity(bdi),
            'readahead_file': {key: value for key, value in ra.items() if key != 'value_kib'},
            'read_ahead_kib': ra['value_kib'], 'other_device_readahead': other, 'mount_empty': empty}


def native_context():
    require(os.environ.get('GITHUB_ACTIONS') == 'true'
            and os.environ.get('RUNNER_ENVIRONMENT') == 'github-hosted'
            and os.environ.get('RUNNER_OS') == 'Linux', 'not a native GitHub-hosted Linux job')
    require(os.environ.get('GITHUB_REPOSITORY') == 'RhudeJJJJ/formal-conjectures'
            and os.environ.get('GITHUB_REF') == 'refs/heads/rg-d1-bothlong-phase-probe-20261104',
            'not the fixed diagnostic repository and branch')
    context = {key: os.environ.get(env) for key, env in zip(
        NATIVE_KEYS, ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_SHA'))}
    require(re.fullmatch(r'[1-9][0-9]*', context['native_run_id'] or '') is not None
            and re.fullmatch(r'[1-9][0-9]*', context['native_run_attempt'] or '') is not None
            and re.fullmatch(r'[0-9a-f]{40}', context['native_workflow_source_commit'] or '') is not None,
            'native run/attempt/head identity unavailable')
    workspace = pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve(strict=True)
    require(workspace.is_relative_to('/home/runner/work') and workspace.is_dir(),
            'unexpected hosted workspace')
    return workspace, context


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('enable', 'check'), required=True)
    args = parser.parse_args()
    workspace, context = native_context()
    image = workspace / 'rg-ephemeral-proofstore.btrfs'
    mount = workspace / 'Proofs/RG_Lean_20261019/build/extension'
    report_path = workspace / (ENABLE_NAME if args.phase == 'enable' else CHECK_NAME)
    require(not report_path.exists() and not report_path.is_symlink(), 'phase report already exists')
    report = {'status': 'OWNED_PROOFSTORE_READAHEAD_REJECTED', 'phase': args.phase,
              'commands': [], 'units': 'read_ahead_kb is KiB (1024 bytes)',
              'proof_export_claim': False, 'resource_limits_changed': False,
              'swap_configuration_changed': False, 'filesystem_recreated_or_remounted': False,
              'only_permitted_mutation': 'one owned Btrfs filesystem BDI read_ahead_kb: positive -> 0',
              'interpretation_limit': 'Compressed extents may still be read in full; this is a bounded hypothesis test.'}
    try:
        dio_source = pathlib.Path(dio.__file__).resolve(strict=True)
        require(dio_source == workspace / 'ci/rg_enable_owned_proofstore_direct_io_20261104.py'
                and sha256(dio_source.read_bytes()) == DIO_HELPER_SHA256,
                'the imported original DIO helper is not byte-identical')
        setup, setup_sha = read_json(workspace / SETUP_NAME)
        dio_report, dio_sha = read_json(workspace / dio.REPORT_NAME)
        validate_inputs(setup, setup_sha, dio_report, context, image, mount)
        kernel = dio.capture(['uname', '--release'], report).strip()
        require(kernel and kernel == dio_report['kernel_release'], 'kernel release changed or unavailable')
        report['binding'] = {**context, 'setup_report_sha256': setup_sha,
                             'dio_report_sha256': dio_sha, 'dio_helper_sha256': DIO_HELPER_SHA256,
                             'helper_sha256': sha256(pathlib.Path(__file__).read_bytes()),
                             'kernel_release': kernel, 'image': str(image), 'mount': str(mount)}
        with os.fdopen(os.open(image, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as stream:
            identity = dio.image_identity(os.fstat(stream.fileno()))
            require(identity['size'] == setup['logical_image_bytes'], 'image size differs from setup')
            current = observe(workspace, image, stream.fileno(), identity, mount, setup, dio_report,
                              report, require_empty=args.phase == 'enable')
            report['before' if args.phase == 'enable' else 'observed'] = current
            print(json.dumps({'phase': args.phase, 'observation': 'before', 'snapshot': current}), flush=True)
            if args.phase == 'enable':
                require(type(current['read_ahead_kib']) is int and current['read_ahead_kib'] > 0,
                        'preexisting zero is not a newly changed readahead experiment')
                target = current['readahead_file']['path']
                # The only mutation: no shell, no device/path argument, no reset or fallback.
                argv = ['sudo', '-n', '--', 'tee', '--', target]
                result = subprocess.run(argv, input='0\n', capture_output=True, text=True, timeout=60,
                                        env={**os.environ, 'LC_ALL': 'C'})
                report['mutation'] = {'argv': argv, 'input': '0\n', 'returncode': result.returncode,
                                      'stdout': result.stdout, 'stderr': result.stderr}
                after = observe(workspace, image, stream.fileno(), identity, mount, setup, dio_report,
                                report, require_empty=True)
                report['after'] = after
                print(json.dumps({'phase': 'enable', 'observation': 'after', 'snapshot': after}), flush=True)
                require(result.returncode == 0 and result.stdout == '0\n' and result.stderr == '',
                        'owned filesystem readahead write did not succeed; no fallback')
                validate_transition(current, after)
                report['status'] = 'OWNED_PROOFSTORE_READAHEAD_ZERO_ENABLED'
            else:
                enabled, enabled_sha = read_json(workspace / ENABLE_NAME)
                report['enable_report_sha256'] = enabled_sha
                validate_enable_report(enabled, report['binding'], current)
                report['status'] = 'OWNED_PROOFSTORE_READAHEAD_ZERO_CONFIRMED'
            require(read_json(workspace / SETUP_NAME)[1] == setup_sha
                    and read_json(workspace / dio.REPORT_NAME)[1] == dio_sha,
                    'setup or DIO report bytes changed during observation')
    except Exception as error:
        report['status'] = 'OWNED_PROOFSTORE_READAHEAD_REJECTED'
        report['error'] = f'{type(error).__name__}: {error}'
        raise
    finally:
        with report_path.open('x') as output:
            json.dump(report, output, indent=2, sort_keys=True)
            output.write('\n')


if __name__ == '__main__':
    main()
