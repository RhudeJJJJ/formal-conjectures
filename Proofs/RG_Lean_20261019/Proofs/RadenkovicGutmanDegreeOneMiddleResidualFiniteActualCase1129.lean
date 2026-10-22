/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1129 : Family 10 := level10.get ⟨1273,by decide⟩
def sourceMap1129 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1129 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1129_checked : acceptsGraphIso
    (source (graph core1129) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2170.graph sourceMap1129=true := by decide +kernel
theorem fusedMap1129_checked : acceptsGraphIso
    (fused (graph core1129) (root 10) 2 2) DegreeTwoThreeSpectrum6537.graph fusedMap1129=true := by decide +kernel
theorem certified1129 : Certified (graph core1129) (root 10) 2 2 :=
  of_native_maps core1129 DegreeOneMiddleResidualSpectrum2170.graph DegreeTwoThreeSpectrum6537.graph
    sourceMap1129 fusedMap1129 sourceMap1129_checked fusedMap1129_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1129
#print axioms sourceMap1129_checked
#print axioms fusedMap1129_checked
#print axioms certified1129
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
