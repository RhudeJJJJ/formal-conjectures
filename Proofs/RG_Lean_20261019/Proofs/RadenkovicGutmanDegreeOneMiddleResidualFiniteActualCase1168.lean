/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1168 : Family 10 := level10.get ⟨1428,by decide⟩
def sourceMap1168 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1168 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1168_checked : acceptsGraphIso
    (source (graph core1168) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2277.graph sourceMap1168=true := by decide +kernel
theorem fusedMap1168_checked : acceptsGraphIso
    (fused (graph core1168) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1951.graph fusedMap1168=true := by decide +kernel
theorem certified1168 : Certified (graph core1168) (root 10) 2 2 :=
  of_native_maps core1168 DegreeOneMiddleResidualSpectrum2277.graph DegreeOneMiddleResidualSpectrum1951.graph
    sourceMap1168 fusedMap1168 sourceMap1168_checked fusedMap1168_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1168
#print axioms sourceMap1168_checked
#print axioms fusedMap1168_checked
#print axioms certified1168
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
