/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1103 : Family 10 := level10.get ⟨1179,by decide⟩
def sourceMap1103 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1103 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1103_checked : acceptsGraphIso
    (source (graph core1103) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2104.graph sourceMap1103=true := by decide +kernel
theorem fusedMap1103_checked : acceptsGraphIso
    (fused (graph core1103) (root 10) 2 2) DegreeTwoThreeSpectrum6344.graph fusedMap1103=true := by decide +kernel
theorem certified1103 : Certified (graph core1103) (root 10) 2 2 :=
  of_native_maps core1103 DegreeOneMiddleResidualSpectrum2104.graph DegreeTwoThreeSpectrum6344.graph
    sourceMap1103 fusedMap1103 sourceMap1103_checked fusedMap1103_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1103
#print axioms sourceMap1103_checked
#print axioms fusedMap1103_checked
#print axioms certified1103
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
