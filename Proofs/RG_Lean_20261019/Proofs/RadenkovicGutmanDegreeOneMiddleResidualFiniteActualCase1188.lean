/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1188 : Family 10 := level10.get ⟨1573,by decide⟩
def sourceMap1188 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1188 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1188_checked : acceptsGraphIso
    (source (graph core1188) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2344.graph sourceMap1188=true := by decide +kernel
theorem fusedMap1188_checked : acceptsGraphIso
    (fused (graph core1188) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1550.graph fusedMap1188=true := by decide +kernel
theorem certified1188 : Certified (graph core1188) (root 10) 2 2 :=
  of_native_maps core1188 DegreeOneMiddleResidualSpectrum2344.graph DegreeOneMiddleResidualSpectrum1550.graph
    sourceMap1188 fusedMap1188 sourceMap1188_checked fusedMap1188_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1188
#print axioms sourceMap1188_checked
#print axioms fusedMap1188_checked
#print axioms certified1188
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
