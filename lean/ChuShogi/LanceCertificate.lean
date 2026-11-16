import ChuShogi.LanceCachedCertificate

/-! Public lance-provider certificate. Regenerate from the repository root:
python3 lean/scripts/generate_lance_certificate.py
python3 lean/scripts/generate_lance_cached_certificate.py

Predecessor edges, stored state codes, complete graph closure and all queried
projections/singletons are ordinary kernel checked. No full promoted-family
classification theorem or native computation oracle is assumed. -/
namespace ChuShogi.LanceCertificate
export LanceCachedCertificate (reach_classified capture_reachable singleton_reachable projected_iff)
end ChuShogi.LanceCertificate
