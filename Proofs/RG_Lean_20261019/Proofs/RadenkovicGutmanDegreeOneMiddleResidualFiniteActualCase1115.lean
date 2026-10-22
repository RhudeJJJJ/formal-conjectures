/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1115 : Family 10 := level10.get ⟨1242,by decide⟩
def sourceMap1115 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1115 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1115_checked : acceptsGraphIso
    (source (graph core1115) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2144.graph sourceMap1115=true := by decide +kernel
theorem fusedMap1115_checked : acceptsGraphIso
    (fused (graph core1115) (root 10) 2 2) DegreeTwoThreeSpectrum6472.graph fusedMap1115=true := by decide +kernel
theorem certified1115 : Certified (graph core1115) (root 10) 2 2 :=
  of_native_maps core1115 DegreeOneMiddleResidualSpectrum2144.graph DegreeTwoThreeSpectrum6472.graph
    sourceMap1115 fusedMap1115 sourceMap1115_checked fusedMap1115_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1115
#print axioms sourceMap1115_checked
#print axioms fusedMap1115_checked
#print axioms certified1115
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
