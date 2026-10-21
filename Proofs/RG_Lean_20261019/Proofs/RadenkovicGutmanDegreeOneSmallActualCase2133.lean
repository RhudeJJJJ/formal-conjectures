/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2133 : Family 10 := level10.get ⟨577,by decide⟩
def sourceMap2133 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2133 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2133_checked : acceptsGraphIso
    (source (graph core2133) (root 10) 0 0) DegreeOneSmallSpectrum1779.graph sourceMap2133=true := by decide +kernel
theorem fusedMap2133_checked : acceptsGraphIso
    (fused (graph core2133) (root 10) 0 0) DegreeOneSmallSpectrum1113.graph fusedMap2133=true := by decide +kernel
theorem certified2133 : Certified (graph core2133) (root 10) 0 0 :=
  of_native_maps core2133 DegreeOneSmallSpectrum1779.graph DegreeOneSmallSpectrum1113.graph
    sourceMap2133 fusedMap2133 sourceMap2133_checked fusedMap2133_checked
    DegreeOneSmallComparisons.comparison2133
#print axioms sourceMap2133_checked
#print axioms fusedMap2133_checked
#print axioms certified2133
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
