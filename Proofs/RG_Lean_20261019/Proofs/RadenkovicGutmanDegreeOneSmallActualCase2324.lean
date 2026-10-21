/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2324 : Family 10 := level10.get ⟨1020,by decide⟩
def sourceMap2324 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2324 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2324_checked : acceptsGraphIso
    (source (graph core2324) (root 10) 0 0) DegreeOneSmallSpectrum1598.graph sourceMap2324=true := by decide +kernel
theorem fusedMap2324_checked : acceptsGraphIso
    (fused (graph core2324) (root 10) 0 0) DegreeOneSmallSpectrum1597.graph fusedMap2324=true := by decide +kernel
theorem certified2324 : Certified (graph core2324) (root 10) 0 0 :=
  of_native_maps core2324 DegreeOneSmallSpectrum1598.graph DegreeOneSmallSpectrum1597.graph
    sourceMap2324 fusedMap2324 sourceMap2324_checked fusedMap2324_checked
    DegreeOneSmallComparisons.comparison2324
#print axioms sourceMap2324_checked
#print axioms fusedMap2324_checked
#print axioms certified2324
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
