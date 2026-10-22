# Attestation and SBOM standards as carriers of formal-verification evidence (state at 2026-10-23)

NOTE: plan mode blocked writing to the requested scratchpad path
(.../scratchpad/research_notes/Certified composition field refresh/attestation_standards.md). Copy this file there once plan mode is off.
Items marked [training] come from model background knowledge and were NOT re-verified this session.

## Q1. Which format best matches "claim + evidence + assumptions", and what is the concrete schema?

### Takeaway
No standard has a first-class "assumptions" field. in-toto SCAI v0.3 is the closest structural fit: `attribute` plus `evidence` plus `conditions`, where `conditions` is a free-form object that could hold the assumption set. CycloneDX 1.6/1.7 `declarations` is the richest claim/evidence model (claims, evidence, counterEvidence, mitigationStrategies, conformance, confidence), but it is built for compliance against a standard's requirements, not for compositional proof obligations. Neither standard enforces union-under-composition or forbids silent discharge, so those invariants would have to live in the predicate's own semantics and verifier.

### Cited Findings
- SCAI v0.3: `predicateType` is `https://in-toto.io/attestation/scai/v0.3`. Shape: `predicate.attributes[]` with `attribute` (string, required), `target` (ResourceDescriptor, optional), `conditions` (object, optional, "conditions under which the attribute arises"), and `evidence` (ResourceDescriptor, optional), plus `predicate.producer` (optional). The formats of `attribute` and `conditions` are left to producer and consumer. The spec asks that semantics stay "consistent and monotonic" across attestations. Its examples are compiler or hardware properties (WITH_STACK_PROTECTION, REPRODUCIBLE, ATTESTED_DEPENDENCIES, VALID_ENCLAVE). Author: Marcela Melara — [in-toto SCAI spec](https://github.com/in-toto/attestation/blob/main/spec/predicates/scai.md)
- SCAI precedent for chaining: `ATTESTED_DEPENDENCIES`, with `target` set to a dependency and `evidence` pointing to that dependency's own attestation (DSSE), is the nearest thing to composing attestations — [SCAI spec](https://github.com/in-toto/attestation/blob/main/spec/predicates/scai.md)
- Simple Verification Result (SVR) v0.2: `https://in-toto.io/attestation/svr/v0.2`. Fields: `verifier.id` (URI), `verifier.policies[]` (ResourceDescriptor, required; bumped to v0.2 to require policies, merged 2026-07-17), `timeCreated`, `properties[]` (strings). It is a summary of "verifier checked X", with no slot for evidence or assumptions — [SVR spec](https://github.com/in-toto/attestation/blob/main/spec/predicates/svr.md); [PR #555](https://github.com/in-toto/attestation/pull/555)
- test-result v0.1: `https://in-toto.io/attestation/test-result/v0.1`. Fields: `result` (PASSED/WARNED/FAILED), `configuration[]` (ResourceDescriptor), `url`, `passedTests[]`, `warnedTests[]`, `failedTests[]` — [test-result spec](https://github.com/in-toto/attestation/blob/main/spec/predicates/test-result.md)
- Vetted in-toto predicates as of now: CycloneDX, Link, Reference, Release, Runtime Traces, SCAI, SLSA Provenance, SLSA VSA, SPDX2, SPDX3, SVR, Test Result, and VULNS (vulns_02) — [predicates README](https://github.com/in-toto/attestation/tree/main/spec/predicates)
- SLSA VSA (`https://slsa.dev/verification_summary/v1`) records the verifier, the verification time, the policy, the input attestations, and the result. It is a policy-check summary, not a proof carrier — [SLSA v1.2 VSA](https://slsa.dev/spec/v1.2/verification_summary)
- CycloneDX `declarations` (since 1.6; 1.7 is current, schema 1.7.1, standardised as ECMA-424 2nd ed., Dec 2025):
  - `assessors[]`
  - `attestations[]`, each with `summary`, `assessor`, `map[]`, and `map[]` entries of {`requirement`, `claims[]`, `counterClaims[]`, `conformance`{`score`, `rationale`, `mitigationStrategies[]`}, `confidence`{`score`, `rationale`}}
  - `claims[]`, each with {`bom-ref`, `target`, `predicate`, `mitigationStrategies[]`, `reasoning`, `evidence[]`, `counterEvidence[]`, `externalReferences[]`, `signature`}
  - `evidence[]`, each with {`propertyName`, `description`, `data[]`{`contents.attachment`, `classification`, `sensitiveData`}, `created`, `expires`, `author`, `reviewer`, `signature`}
  - `targets`, and `affirmation`{`statement`, `signatories[]`}
  - Requirements come from `definitions.standards` [training: standards → requirements tree].
  - Sources: [CycloneDX attestations use case](https://cyclonedx.org/use-cases/attestations); [ECMA-424](https://ecma-international.org/publications-and-standards/standards/ecma-424/); [OWASP CDXA announcement 2023-12](https://owasp.org/blog/2023/12/06/CycloneDX-attestations)
- CycloneDX evidence can live in a separate BOM from the attestation, which allows restricted access to sensitive evidence — [CycloneDX evidence management](https://cyclonedx.org/use-cases/evidence-management)
- SPDX 3.0.1 profiles: Core, Software, Security, Licensing (Simple/Expanded), Dataset, AI, Build, Lite, Extension. Security covers VEX relationships (affected / notAffected / fixed / underInvestigation, with `justificationType`) and CVSS v2/v3/v4, EPSS, exploit catalog, and SSVC. Extension has `Extension` and `CdxPropertiesExtension`. There is no claim/evidence/assurance class — [SPDX 3.0.1 spec](https://spdx.github.io/spdx-spec/v3.0.1/)
- OSCAL assessment-results: observations ("individual observations and evidence"), findings (with objective status), and risks. It supports continuous and snapshot assessment and feeds residual risk into POA&M. It is control-catalog oriented (the FedRAMP SAR use) — [NIST OSCAL assessment results](https://pages.nist.gov/OSCAL/learn/concepts/layer/assessment/assessment-results); [FedRAMP SAR](https://automate.fedramp.gov/documentation/sar/3-working-with-oscal-files)
- OpenVEX / CSAF VEX [training]: per-(product, vulnerability) status of not_affected, affected, fixed, or under_investigation. not_affected justifications include `vulnerable_code_not_present`, `vulnerable_code_not_in_execute_path`, `vulnerable_code_cannot_be_controlled_by_adversary`, and `inline_mitigations_already_exist`. A proof of absence of a bug class could back a not_affected justification, but VEX is keyed to CVEs, not to properties.

### Inferences
- Best fit for the ledger: a custom in-toto predicate that reuses the SCAI pattern. Each entry is (property, target, evidence = proof artifact or toolchain, conditions = assumptions). The new predicate would add the semantics SCAI lacks: assumptions as a typed set, union under composition, and "no discharge without a discharging attestation". Alternatively, ship it as plain SCAI with a documented `conditions` sub-schema, which needs no registration.
- Use CycloneDX `declarations` as the export/compliance view, mapping each ledger claim to a `claim`, the proof to `evidence`, and assumptions to `reasoning`/`mitigationStrategies` or a dedicated `counterClaims` convention. This is lossy, because there is no structural field for assumptions.
- SVR or VSA can sit downstream as a policy-gate summary ("verifier accepted ledger L under policy P").

### Gaps
- I found no standard field named or meant for "assumptions" or "hypotheses" in any of the formats.
- I did not fetch the CycloneDX 1.7 `definitions.standards` JSON schema directly.

## Q2. Process and timeline to register a new in-toto predicate type

### Takeaway
Anyone can open a PR (ITE-9 format plus the predicate template). Maintainers review it, and its status is discussed at the monthly community meeting. There is no published SLA. In practice, maintainer-driven predicate changes merge in about 1 to 8 weeks, while third-party community predicates have been piling up unmerged through 2026.

### Cited Findings
- The steps are:
  1. Answer the preliminary questions: use case, why existing predicates are insufficient, an example (JSON/CUE), and the policy questions.
  2. Follow the conventions: lowerCamelCase, RFC 3339 "Z" timestamps.
  3. The author writes the spec ("Your predicate is yours").
  4. Open a PR in ITE-9 format with the template, and add a protobuf for Go/Python/Java bindings.
  5. Maintainers review it, with status discussed at the monthly meeting.
  6. If accepted, it is added to the directory.
  7. If the predicate uses the in-toto.io namespace, add a redirect PR to the in-toto.io redirects list.
  - The process is described as "short" with no timeline — [new predicate guidelines](https://github.com/in-toto/attestation/blob/main/docs/new_predicate_guidelines.md); [ITE-9](https://github.com/in-toto/ITE/blob/master/ITE/9/README.adoc)
- Merge latencies seen (gh, 2026-10-23):
  - SPDX3 predicate: 2025-12-02 to 2026-01-22 (~7 weeks) — [PR #508](https://github.com/in-toto/attestation/pull/508)
  - SVR v0.2: 2026-05-21 to 2026-07-17 (~8 weeks) — [PR #555](https://github.com/in-toto/attestation/pull/555)
  - Reference predicate: 2024-08-01 to 2024-10-02 (~9 weeks) — [PR #375](https://github.com/in-toto/attestation/pull/375)
  - Release v0.2: 1 week — [PR #495](https://github.com/in-toto/attestation/pull/495)
- Backlog: 21 open PRs, most of them new community predicates from 2026, none merged. They include:
  - source-review-coverage (07-28) — [#581](https://github.com/in-toto/attestation/pull/581)
  - Adversarial Execution Evidence v0.7 (07-15) — [#570](https://github.com/in-toto/attestation/pull/570)
  - eval-result (07-23) — [#575](https://github.com/in-toto/attestation/pull/575)
  - PRML (08-18) — [#587](https://github.com/in-toto/attestation/pull/587)
  - AI Agent Decision/Action — [#591](https://github.com/in-toto/attestation/pull/591), [#588](https://github.com/in-toto/attestation/pull/588)
  - Computation Receipt (09-06; 14 comments, 7 reviews) — [#592](https://github.com/in-toto/attestation/pull/592)
  - AI Change Provenance/Authorship/Review — [#601](https://github.com/in-toto/attestation/pull/601)–[#603](https://github.com/in-toto/attestation/pull/603)
  - Observed Effect — [#607](https://github.com/in-toto/attestation/pull/607)
  - Agentic process evidence — [#609](https://github.com/in-toto/attestation/pull/609)
  - Some similar ones were closed: OCG Execution Receipt [#567](https://github.com/in-toto/attestation/pull/567) and Decision Receipt [#549](https://github.com/in-toto/attestation/pull/549)
- Open PR #597 (2026-09-23, 0 reviews) proposes an executable conformance-vector layer for every predicate. It notes that none of the 15 predicate docs ships conformance vectors — [PR #597](https://github.com/in-toto/attestation/pull/597)
- An earlier human-review predicate attempt (PR #151, issue #77) was closed without a merge — [#151](https://github.com/in-toto/attestation/pull/151); [#77](https://github.com/in-toto/attestation/issues/77)
- Registration is not required to use a predicate type. Any TypeURI works, and cosign/GitHub accept custom types [training: `cosign attest --type <URI> --predicate file.json`; `actions/attest` with `predicate-type` + `predicate-path`; `gh attestation verify --predicate-type`] — [Sigstore in-toto attestations](https://docs.sigstore.dev/cosign/verifying/attestation/)

### Inferences
- Realistic plan: publish under your own TypeURI now (it works today with cosign, GitHub, and Rekor), then open an ITE-9 PR. Expect at least 2 to 3 months, and possibly indefinite, given the 2026 backlog of unmerged community predicates. Shipping conformance vectors and a protobuf would set the proposal apart (compare #597). Proposing it as an extension or profile of SCAI `conditions` may be the lower-friction route, since SCAI is maintained by a core author.
- Search terms "formal", "proof" and "lean" turned up no formal-verification predicate in the repo, so the niche is open.

### Gaps
- Maintainer meeting minutes for 2026 were not read, so I don't know whether the community-predicate backlog is policy (for example a freeze) or just capacity.

## Q3. SLSA, Sigstore and GitHub status

### Cited Findings
- SLSA v1.2 was released in November 2025. It adds the Source Track and is backward compatible with v1.1. After RC1, Source L2 was refocused on history and provenance, and L3 on continuous enforcement of technical controls. Next in development: the Build Environment Track and the Dependency Track — [SLSA v1.2 announcement](https://slsa.dev/blog/2025/11/announce-slsa-v1.2); [What's new](https://slsa.dev/spec/v1.2/whats-new)
- SLSA leaves source provenance attestations "undefined and up to the SCSs", as cited in [#581](https://github.com/in-toto/attestation/pull/581)
- I found no SLSA track covering verification or assurance of artifact properties. SLSA is about integrity of process, not correctness of the artifact.
- Sigstore: cosign signs and verifies in-toto attestations of arbitrary predicate types and can check predicates against CUE/Rego policies — [Sigstore docs](https://docs.sigstore.dev/cosign/verifying/attestation/)
- GitHub artifact attestations [training]: GA since mid-2024. `actions/attest-build-provenance` and `actions/attest-sbom` cover the standard types, and the generic `actions/attest` takes a custom predicate. Signing is Sigstore-backed (public-good Rekor for public repos, GitHub's own instance for private), and `gh attestation verify` checks them.

## Q4. Is anyone already producing verification-evidence attestations?

### Takeaway
I found no public example from AWS, Google, Galois, AdaCore, or AbsInt of formal-proof results packaged as in-toto, CycloneDX, or SPDX attestations. Formal-methods evidence is published as reproducible proof repositories and papers, not as supply-chain metadata.

### Cited Findings
- AWS and Galois published machine-assisted proofs (AES-256-GCM, SHA-384) using SAW and Cryptol. s2n-bignum ships the proof sources and scripts for reproduction, which is evidence as a repo, not an attestation — [AWS/Galois "Verified Cryptographic Code for Everybody"](https://assets.amazon.science/4e/23/177acd514c799204ae22f98e193d/verified-cryptographic-code-for-everybody.pdf); [NIST: Formal verification of crypto at AWS](https://www.nist.gov/document/formal-verification-cryptographic-software-aws-current-practices-and-future-trends)
- The nearest analogues in the in-toto queue are re-executable-correctness or evidence predicates: Computation Receipt (numeric results checkable by re-execution) and Adversarial Execution Evidence. Neither is about proofs — [#592](https://github.com/in-toto/attestation/pull/592); [#570](https://github.com/in-toto/attestation/pull/570)
- Targeted searches ("formal verification attestation in-toto", "proof attestation SBOM", "CycloneDX attestation formal methods") returned only generic supply-chain material.

### Gaps
- I did not check AdaCore (SPARK/GNATprove), AbsInt (Astrée/CompCert qualification kits), or TrustInSoft for SBOM integrations directly. Their evidence is traditionally DO-178C/ISO 26262 qualification kits [training].

## Q5. Regulatory demand (CRA, CISA, NIST) and acceptance of formal methods

### Takeaway
CRA reporting started on 11 Sep 2026. No CRA harmonised standard is cited in the OJ yet, and draft delivery deadlines are proposed to slip to 31 Oct and 31 Dec 2026. SSDF 1.2 is still a draft. I found no 2026 CISA formal-methods guidance and no regulator text that explicitly accepts machine-checked proofs as conformity evidence.

### Cited Findings
- CRA: reporting of actively exploited vulnerabilities and severe incidents to the CSIRT and ENISA through the Art. 16 single reporting platform has applied since 11 Sep 2026. It is decoupled from standards. Main obligations apply from 11 Dec 2027 — [cyberresilienceact.eu](https://www.cyberresilienceact.eu/news/cra-standardisation-deadlines-pushed-back-two-months.html) (secondhand); [BSI CRA page](https://www.bsi.bund.de/EN/Themen/Unternehmen-und-Organisationen/Informationen-und-Empfehlungen/Cyber_Resilience_Act/cyber_resilience_act_node.html)
- Standardisation request M/606 (C(2025)618, Feb 2025) was accepted by CEN, CENELEC and ETSI. A draft Commission amendment moves draft delivery:
  - Type A (horizontal) and Type B (vulnerability management): 30 Aug 2026 to 31 Oct 2026
  - Type C (product-specific): 30 Oct 2026 to 31 Dec 2026
  - As of 11 Sep 2026 the amendment was not adopted or published in the OJ. Secondhand: [cyberresilienceact.eu (30 Jul, updated 11 Sep 2026)](https://www.cyberresilienceact.eu/news/cra-standardisation-deadlines-pushed-back-two-months.html); [Cyber Cert Labs](https://www.cybercertlabs.com/case-studies/the-cra-harmonised-standards-landscape-explained/)
- Standards in progress:
  - EN 40000 series (CEN/CLC JTC 13 WG9), with prEN 40000-1-3 (vulnerability handling) expected to be cited first; some parts are not due until autumn 2027
  - prEN 50770 for Annex III OT products, based on IEC 62443
  - ETSI public enquiry on 17 product standards opened 13 Aug 2026
  - No harmonised standard cited in the OJ, so there is no Art. 27 presumption of conformity yet
  - Source (secondhand): [cyberresilienceact.eu](https://www.cyberresilienceact.eu/news/cra-standardisation-deadlines-pushed-back-two-months.html)
- CRA technical documentation [training]: Annex VII requires the technical documentation, including the SBOM (Annex I Part II requires a machine-readable SBOM of at least top-level dependencies) and test/assessment reports. The text names no SBOM format, and formal methods are neither required nor named.
- NIST SSDF 1.2 (SP 800-218 Rev.1) was released as an initial public draft on 2025-12-17 under EO 14306. Comments closed 2026-01-30. It was still listed as Draft at the time of the search, with v1.1 (2022) the final version — [NIST SSDF publications](https://csrc.nist.gov/Projects/ssdf/publications); [SP 800-218r1 ipd](https://csrc.nist.gov/pubs/sp/800/218/r1/ipd)
- CISA: the latest found is the June 2025 CISA/NSA guide on memory-safe languages. The Product Security Bad Practices guidance set 1 Jan 2026 as the date to have a memory-safety roadmap, and it is voluntary. I found no 2026 CISA item on formal methods — [CISA June 2025](https://www.cisa.gov/news-events/alerts/2025/06/24/new-guidance-released-reducing-memory-related-vulnerabilities); [TechRepublic](https://techrepublic.com/article/cisa-fbi-memory-safety-recommendations) (secondhand)

### Inferences
- Demand is for SBOMs, vulnerability handling, and reporting, not for property proofs. A proof ledger enters CRA compliance as supporting material in the Annex VII technical documentation, or as backing for VEX not_affected claims. That second route is the most concrete regulatory hook: a proof of absence of a bug class supports `vulnerable_code_not_present` or `inline_mitigations_already_exist`.
- Harmonised standards are still being written (drafts due 31 Oct / 31 Dec 2026 if the amendment is adopted), so there is a narrow window to get formal-verification evidence mentioned in the EN 40000 generic-controls parts, which run to autumn 2027.

### Gaps
- EUR-Lex and the Commission's standardisation page were not fetched directly. CRA details are from secondhand trackers plus training.
- The status of the ENISA single reporting platform after go-live was not verified (Industrial Cyber returned 403).
- I found no regulator (EU, US, UK NCSC) text explicitly accepting machine-checked proofs as evidence in this round. Common Criteria EAL7 and DO-178C DO-333 are the long-standing precedents [training].
