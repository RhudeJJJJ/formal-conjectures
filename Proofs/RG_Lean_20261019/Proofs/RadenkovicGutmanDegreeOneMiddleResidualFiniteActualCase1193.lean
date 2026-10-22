/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1193 : Family 10 := level10.get ⟨1617,by decide⟩
def sourceMap1193 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1193 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1193_checked : acceptsGraphIso
    (source (graph core1193) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2349.graph sourceMap1193=true := by decide +kernel
theorem fusedMap1193_checked : acceptsGraphIso
    (fused (graph core1193) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1596.graph fusedMap1193=true := by decide +kernel
theorem certified1193 : Certified (graph core1193) (root 10) 2 2 :=
  of_native_maps core1193 DegreeOneMiddleResidualSpectrum2349.graph DegreeOneMiddleResidualSpectrum1596.graph
    sourceMap1193 fusedMap1193 sourceMap1193_checked fusedMap1193_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1193
#print axioms sourceMap1193_checked
#print axioms fusedMap1193_checked
#print axioms certified1193
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
