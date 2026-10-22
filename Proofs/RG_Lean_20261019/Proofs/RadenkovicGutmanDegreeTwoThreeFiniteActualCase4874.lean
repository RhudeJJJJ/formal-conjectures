/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4874 : Family 10 := level10.get ⟨1311,by decide⟩
def sourceMap4874 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4874 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4874_checked : acceptsGraphIso
    (source (graph core4874) (root 10) 2 2) DegreeTwoThreeSpectrum7392.graph sourceMap4874=true := by decide +kernel
theorem fusedMap4874_checked : acceptsGraphIso
    (fused (graph core4874) (root 10) 2 2) DegreeTwoThreeSpectrum6609.graph fusedMap4874=true := by decide +kernel
theorem certified4874 : Certified (graph core4874) (root 10) 2 2 :=
  of_native_maps core4874 DegreeTwoThreeSpectrum7392.graph DegreeTwoThreeSpectrum6609.graph
    sourceMap4874 fusedMap4874 sourceMap4874_checked fusedMap4874_checked
    DegreeTwoThreeFiniteComparisons.comparison4874
#print axioms sourceMap4874_checked
#print axioms fusedMap4874_checked
#print axioms certified4874
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
