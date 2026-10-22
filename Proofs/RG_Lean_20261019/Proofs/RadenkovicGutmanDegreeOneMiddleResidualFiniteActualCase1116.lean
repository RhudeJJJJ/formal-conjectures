/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1116 : Family 10 := level10.get ⟨1244,by decide⟩
def sourceMap1116 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1116 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1116_checked : acceptsGraphIso
    (source (graph core1116) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2146.graph sourceMap1116=true := by decide +kernel
theorem fusedMap1116_checked : acceptsGraphIso
    (fused (graph core1116) (root 10) 2 2) DegreeTwoThreeSpectrum6478.graph fusedMap1116=true := by decide +kernel
theorem certified1116 : Certified (graph core1116) (root 10) 2 2 :=
  of_native_maps core1116 DegreeOneMiddleResidualSpectrum2146.graph DegreeTwoThreeSpectrum6478.graph
    sourceMap1116 fusedMap1116 sourceMap1116_checked fusedMap1116_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1116
#print axioms sourceMap1116_checked
#print axioms fusedMap1116_checked
#print axioms certified1116
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
