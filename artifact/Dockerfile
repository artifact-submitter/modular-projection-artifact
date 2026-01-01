# syntax=docker/dockerfile:1
# Deliberately no default: callers must supply an immutable, digest-pinned
# Linux image with a compatible userspace and Python 3.11 or newer.  The proof
# archive supplies the exact Lean toolchain recorded in its manifest.
ARG BASE_IMAGE
FROM ${BASE_IMAGE}

USER root
RUN install -d -m 0755 /opt/certifiedjl/scripts /workspace
# Install the complete trusted verifier dependency closure before inspecting an
# archive.  Verification never imports Python from the untrusted archive.
COPY scripts/proof_bundle.py /opt/certifiedjl/scripts/
COPY scripts/release_validation.py /opt/certifiedjl/scripts/
COPY scripts/native_shadow_replay.py /opt/certifiedjl/scripts/
COPY scripts/reviewer_workspace.py /opt/certifiedjl/scripts/
COPY scripts/lean_source.py /opt/certifiedjl/scripts/
COPY scripts/compute_replay_digest.py /opt/certifiedjl/scripts/
COPY scripts/check_replay_families.py /opt/certifiedjl/scripts/
COPY artifact/entrypoint.sh /opt/certifiedjl/entrypoint.sh
RUN chmod 0755 /opt/certifiedjl/scripts/proof_bundle.py /opt/certifiedjl/entrypoint.sh

WORKDIR /workspace
ENTRYPOINT ["/opt/certifiedjl/entrypoint.sh"]
