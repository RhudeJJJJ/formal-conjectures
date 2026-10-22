/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0266 : Family 9 := level9.get ⟨350,by decide⟩
def sourceMap0266 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0266 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0266_checked : acceptsGraphIso
    (source (graph core0266) (root 9) 0 0) DegreeOneSmallSpectrum425.graph sourceMap0266=true := by decide +kernel
theorem fusedMap0266_checked : acceptsGraphIso
    (fused (graph core0266) (root 9) 0 0) DegreeOneSmallSpectrum424.graph fusedMap0266=true := by decide +kernel
theorem certified0266 : Certified (graph core0266) (root 9) 0 0 :=
  of_native_maps core0266 DegreeOneSmallSpectrum425.graph DegreeOneSmallSpectrum424.graph
    sourceMap0266 fusedMap0266 sourceMap0266_checked fusedMap0266_checked
    DegreeTwoThreeFiniteComparisons.comparison0266
#print axioms sourceMap0266_checked
#print axioms fusedMap0266_checked
#print axioms certified0266
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
