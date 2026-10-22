/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1166 : Family 10 := level10.get ⟨1425,by decide⟩
def sourceMap1166 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1166 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1166_checked : acceptsGraphIso
    (source (graph core1166) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2274.graph sourceMap1166=true := by decide +kernel
theorem fusedMap1166_checked : acceptsGraphIso
    (fused (graph core1166) (root 10) 2 2) DegreeTwoThreeSpectrum6880.graph fusedMap1166=true := by decide +kernel
theorem certified1166 : Certified (graph core1166) (root 10) 2 2 :=
  of_native_maps core1166 DegreeOneMiddleResidualSpectrum2274.graph DegreeTwoThreeSpectrum6880.graph
    sourceMap1166 fusedMap1166 sourceMap1166_checked fusedMap1166_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1166
#print axioms sourceMap1166_checked
#print axioms fusedMap1166_checked
#print axioms certified1166
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
