/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1043 : Family 10 := level10.get ⟨1022,by decide⟩
def sourceMap1043 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1043 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1043_checked : acceptsGraphIso
    (source (graph core1043) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1982.graph sourceMap1043=true := by decide +kernel
theorem fusedMap1043_checked : acceptsGraphIso
    (fused (graph core1043) (root 10) 2 2) DegreeTwoThreeSpectrum6028.graph fusedMap1043=true := by decide +kernel
theorem certified1043 : Certified (graph core1043) (root 10) 2 2 :=
  of_native_maps core1043 DegreeOneMiddleResidualSpectrum1982.graph DegreeTwoThreeSpectrum6028.graph
    sourceMap1043 fusedMap1043 sourceMap1043_checked fusedMap1043_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1043
#print axioms sourceMap1043_checked
#print axioms fusedMap1043_checked
#print axioms certified1043
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
