/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2309 : Family 10 := level10.get ⟨995,by decide⟩
def sourceMap2309 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2309 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2309_checked : acceptsGraphIso
    (source (graph core2309) (root 10) 0 0) DegreeOneSmallSpectrum1519.graph sourceMap2309=true := by decide +kernel
theorem fusedMap2309_checked : acceptsGraphIso
    (fused (graph core2309) (root 10) 0 0) DegreeOneSmallSpectrum1521.graph fusedMap2309=true := by decide +kernel
theorem certified2309 : Certified (graph core2309) (root 10) 0 0 :=
  of_native_maps core2309 DegreeOneSmallSpectrum1519.graph DegreeOneSmallSpectrum1521.graph
    sourceMap2309 fusedMap2309 sourceMap2309_checked fusedMap2309_checked
    DegreeOneSmallComparisons.comparison2309
#print axioms sourceMap2309_checked
#print axioms fusedMap2309_checked
#print axioms certified2309
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
