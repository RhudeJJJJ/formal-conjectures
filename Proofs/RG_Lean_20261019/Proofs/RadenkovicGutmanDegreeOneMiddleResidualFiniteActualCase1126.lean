/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1126 : Family 10 := level10.get ⟨1269,by decide⟩
def sourceMap1126 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1126 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1126_checked : acceptsGraphIso
    (source (graph core1126) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2166.graph sourceMap1126=true := by decide +kernel
theorem fusedMap1126_checked : acceptsGraphIso
    (fused (graph core1126) (root 10) 2 2) DegreeTwoThreeSpectrum6529.graph fusedMap1126=true := by decide +kernel
theorem certified1126 : Certified (graph core1126) (root 10) 2 2 :=
  of_native_maps core1126 DegreeOneMiddleResidualSpectrum2166.graph DegreeTwoThreeSpectrum6529.graph
    sourceMap1126 fusedMap1126 sourceMap1126_checked fusedMap1126_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1126
#print axioms sourceMap1126_checked
#print axioms fusedMap1126_checked
#print axioms certified1126
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
