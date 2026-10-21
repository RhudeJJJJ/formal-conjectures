/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2242 : Family 10 := level10.get ⟨790,by decide⟩
def sourceMap2242 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2242 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2242_checked : acceptsGraphIso
    (source (graph core2242) (root 10) 0 0) DegreeOneSmallSpectrum1752.graph sourceMap2242=true := by decide +kernel
theorem fusedMap2242_checked : acceptsGraphIso
    (fused (graph core2242) (root 10) 0 0) DegreeOneSmallSpectrum1429.graph fusedMap2242=true := by decide +kernel
theorem certified2242 : Certified (graph core2242) (root 10) 0 0 :=
  of_native_maps core2242 DegreeOneSmallSpectrum1752.graph DegreeOneSmallSpectrum1429.graph
    sourceMap2242 fusedMap2242 sourceMap2242_checked fusedMap2242_checked
    DegreeOneSmallComparisons.comparison2242
#print axioms sourceMap2242_checked
#print axioms fusedMap2242_checked
#print axioms certified2242
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
