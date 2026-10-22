/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4852 : Family 10 := level10.get ⟨1260,by decide⟩
def sourceMap4852 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4852 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4852_checked : acceptsGraphIso
    (source (graph core4852) (root 10) 2 2) DegreeTwoThreeSpectrum7343.graph sourceMap4852=true := by decide +kernel
theorem fusedMap4852_checked : acceptsGraphIso
    (fused (graph core4852) (root 10) 2 2) DegreeTwoThreeSpectrum6511.graph fusedMap4852=true := by decide +kernel
theorem certified4852 : Certified (graph core4852) (root 10) 2 2 :=
  of_native_maps core4852 DegreeTwoThreeSpectrum7343.graph DegreeTwoThreeSpectrum6511.graph
    sourceMap4852 fusedMap4852 sourceMap4852_checked fusedMap4852_checked
    DegreeTwoThreeFiniteComparisons.comparison4852
#print axioms sourceMap4852_checked
#print axioms fusedMap4852_checked
#print axioms certified4852
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
