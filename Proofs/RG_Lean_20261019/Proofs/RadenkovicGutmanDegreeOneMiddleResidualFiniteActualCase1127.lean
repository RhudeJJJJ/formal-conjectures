/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1127 : Family 10 := level10.get ⟨1270,by decide⟩
def sourceMap1127 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1127 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1127_checked : acceptsGraphIso
    (source (graph core1127) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2167.graph sourceMap1127=true := by decide +kernel
theorem fusedMap1127_checked : acceptsGraphIso
    (fused (graph core1127) (root 10) 2 2) DegreeTwoThreeSpectrum6531.graph fusedMap1127=true := by decide +kernel
theorem certified1127 : Certified (graph core1127) (root 10) 2 2 :=
  of_native_maps core1127 DegreeOneMiddleResidualSpectrum2167.graph DegreeTwoThreeSpectrum6531.graph
    sourceMap1127 fusedMap1127 sourceMap1127_checked fusedMap1127_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1127
#print axioms sourceMap1127_checked
#print axioms fusedMap1127_checked
#print axioms certified1127
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
