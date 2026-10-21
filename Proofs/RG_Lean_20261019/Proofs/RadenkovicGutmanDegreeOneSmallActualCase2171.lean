/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2171 : Family 10 := level10.get ⟨643,by decide⟩
def sourceMap2171 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2171 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2171_checked : acceptsGraphIso
    (source (graph core2171) (root 10) 0 0) DegreeOneSmallSpectrum1747.graph sourceMap2171=true := by decide +kernel
theorem fusedMap2171_checked : acceptsGraphIso
    (fused (graph core2171) (root 10) 0 0) DegreeOneSmallSpectrum1241.graph fusedMap2171=true := by decide +kernel
theorem certified2171 : Certified (graph core2171) (root 10) 0 0 :=
  of_native_maps core2171 DegreeOneSmallSpectrum1747.graph DegreeOneSmallSpectrum1241.graph
    sourceMap2171 fusedMap2171 sourceMap2171_checked fusedMap2171_checked
    DegreeOneSmallComparisons.comparison2171
#print axioms sourceMap2171_checked
#print axioms fusedMap2171_checked
#print axioms certified2171
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
