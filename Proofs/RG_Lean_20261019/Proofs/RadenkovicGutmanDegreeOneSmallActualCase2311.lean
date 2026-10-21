/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2311 : Family 10 := level10.get ⟨997,by decide⟩
def sourceMap2311 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2311 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2311_checked : acceptsGraphIso
    (source (graph core2311) (root 10) 0 0) DegreeOneSmallSpectrum1527.graph sourceMap2311=true := by decide +kernel
theorem fusedMap2311_checked : acceptsGraphIso
    (fused (graph core2311) (root 10) 0 0) DegreeOneSmallSpectrum1531.graph fusedMap2311=true := by decide +kernel
theorem certified2311 : Certified (graph core2311) (root 10) 0 0 :=
  of_native_maps core2311 DegreeOneSmallSpectrum1527.graph DegreeOneSmallSpectrum1531.graph
    sourceMap2311 fusedMap2311 sourceMap2311_checked fusedMap2311_checked
    DegreeOneSmallComparisons.comparison2311
#print axioms sourceMap2311_checked
#print axioms fusedMap2311_checked
#print axioms certified2311
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
