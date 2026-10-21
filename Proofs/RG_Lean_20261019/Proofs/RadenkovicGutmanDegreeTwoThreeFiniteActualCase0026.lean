/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0026 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap0026 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap0026 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0026_checked : acceptsGraphIso
    (source (graph core0026) (root 6) 0 0) DegreeOneSmallSpectrum070.graph sourceMap0026=true := by decide +kernel
theorem fusedMap0026_checked : acceptsGraphIso
    (fused (graph core0026) (root 6) 0 0) DegreeOneSmallSpectrum069.graph fusedMap0026=true := by decide +kernel
theorem certified0026 : Certified (graph core0026) (root 6) 0 0 :=
  of_native_maps core0026 DegreeOneSmallSpectrum070.graph DegreeOneSmallSpectrum069.graph
    sourceMap0026 fusedMap0026 sourceMap0026_checked fusedMap0026_checked
    DegreeTwoThreeFiniteComparisons.comparison0026
#print axioms sourceMap0026_checked
#print axioms fusedMap0026_checked
#print axioms certified0026
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
