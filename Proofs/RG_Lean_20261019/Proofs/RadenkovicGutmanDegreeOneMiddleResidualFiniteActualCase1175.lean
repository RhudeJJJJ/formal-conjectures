/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1175 : Family 10 := level10.get ⟨1526,by decide⟩
def sourceMap1175 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1175 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1175_checked : acceptsGraphIso
    (source (graph core1175) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2331.graph sourceMap1175=true := by decide +kernel
theorem fusedMap1175_checked : acceptsGraphIso
    (fused (graph core1175) (root 10) 2 2) DegreeTwoThreeSpectrum5962.graph fusedMap1175=true := by decide +kernel
theorem certified1175 : Certified (graph core1175) (root 10) 2 2 :=
  of_native_maps core1175 DegreeOneMiddleResidualSpectrum2331.graph DegreeTwoThreeSpectrum5962.graph
    sourceMap1175 fusedMap1175 sourceMap1175_checked fusedMap1175_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1175
#print axioms sourceMap1175_checked
#print axioms fusedMap1175_checked
#print axioms certified1175
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
