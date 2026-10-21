/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2216 : Family 10 := level10.get ⟨741,by decide⟩
def sourceMap2216 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2216 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2216_checked : acceptsGraphIso
    (source (graph core2216) (root 10) 0 0) DegreeOneSmallSpectrum1827.graph sourceMap2216=true := by decide +kernel
theorem fusedMap2216_checked : acceptsGraphIso
    (fused (graph core2216) (root 10) 0 0) DegreeOneSmallSpectrum1369.graph fusedMap2216=true := by decide +kernel
theorem certified2216 : Certified (graph core2216) (root 10) 0 0 :=
  of_native_maps core2216 DegreeOneSmallSpectrum1827.graph DegreeOneSmallSpectrum1369.graph
    sourceMap2216 fusedMap2216 sourceMap2216_checked fusedMap2216_checked
    DegreeOneSmallComparisons.comparison2216
#print axioms sourceMap2216_checked
#print axioms fusedMap2216_checked
#print axioms certified2216
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
