/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2093 : Family 10 := level10.get ⟨508,by decide⟩
def sourceMap2093 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2093 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2093_checked : acceptsGraphIso
    (source (graph core2093) (root 10) 0 0) DegreeOneSmallSpectrum1593.graph sourceMap2093=true := by decide +kernel
theorem fusedMap2093_checked : acceptsGraphIso
    (fused (graph core2093) (root 10) 0 0) DegreeOneSmallSpectrum994.graph fusedMap2093=true := by decide +kernel
theorem certified2093 : Certified (graph core2093) (root 10) 0 0 :=
  of_native_maps core2093 DegreeOneSmallSpectrum1593.graph DegreeOneSmallSpectrum994.graph
    sourceMap2093 fusedMap2093 sourceMap2093_checked fusedMap2093_checked
    DegreeOneSmallComparisons.comparison2093
#print axioms sourceMap2093_checked
#print axioms fusedMap2093_checked
#print axioms certified2093
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
