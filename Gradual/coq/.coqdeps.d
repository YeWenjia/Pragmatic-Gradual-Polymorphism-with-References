LibTactics.vo LibTactics.glob LibTactics.v.beautified: LibTactics.v
LibTactics.vio: LibTactics.v
Definitions.vo Definitions.glob Definitions.v.beautified: Definitions.v
Definitions.vio: Definitions.v
Infrastructure.vo Infrastructure.glob Infrastructure.v.beautified: Infrastructure.v Definitions.vo LibTactics.vo
Infrastructure.vio: Infrastructure.v Definitions.vio LibTactics.vio
Lemmas.vo Lemmas.glob Lemmas.v.beautified: Lemmas.v LibTactics.vo Definitions.vo Infrastructure.vo
Lemmas.vio: Lemmas.v LibTactics.vio Definitions.vio Infrastructure.vio
Soundness.vo Soundness.glob Soundness.v.beautified: Soundness.v LibTactics.vo Definitions.vo Infrastructure.vo Lemmas.vo
Soundness.vio: Soundness.v LibTactics.vio Definitions.vio Infrastructure.vio Lemmas.vio
Determinism.vo Determinism.glob Determinism.v.beautified: Determinism.v LibTactics.vo Definitions.vo Lemmas.vo Infrastructure.vo Soundness.vo
Determinism.vio: Determinism.v LibTactics.vio Definitions.vio Lemmas.vio Infrastructure.vio Soundness.vio
Static.vo Static.glob Static.v.beautified: Static.v LibTactics.vo Definitions.vo Infrastructure.vo Lemmas.vo Determinism.vo Soundness.vo
Static.vio: Static.v LibTactics.vio Definitions.vio Infrastructure.vio Lemmas.vio Determinism.vio Soundness.vio
Criteria.vo Criteria.glob Criteria.v.beautified: Criteria.v LibTactics.vo Definitions.vo Infrastructure.vo Lemmas.vo Determinism.vo Soundness.vo
Criteria.vio: Criteria.v LibTactics.vio Definitions.vio Infrastructure.vio Lemmas.vio Determinism.vio Soundness.vio
