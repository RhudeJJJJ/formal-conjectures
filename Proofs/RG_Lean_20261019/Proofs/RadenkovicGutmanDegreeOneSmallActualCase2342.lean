/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2342 : Family 10 := level10.get ⟨1055,by decide⟩
def sourceMap2342 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2342 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2342_checked : acceptsGraphIso
    (source (graph core2342) (root 10) 0 0) DegreeOneSmallSpectrum1656.graph sourceMap2342=true := by decide +kernel
theorem fusedMap2342_checked : acceptsGraphIso
    (fused (graph core2342) (root 10) 0 0) DegreeOneSmallSpectrum1668.graph fusedMap2342=true := by decide +kernel
theorem certified2342 : Certified (graph core2342) (root 10) 0 0 :=
  of_native_maps core2342 DegreeOneSmallSpectrum1656.graph DegreeOneSmallSpectrum1668.graph
    sourceMap2342 fusedMap2342 sourceMap2342_checked fusedMap2342_checked
    DegreeOneSmallComparisons.comparison2342
#print axioms sourceMap2342_checked
#print axioms fusedMap2342_checked
#print axioms certified2342
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
