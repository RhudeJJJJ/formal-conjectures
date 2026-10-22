/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4480 : Family 10 := level10.get ⟨213,by decide⟩
def sourceMap4480 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4480 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4480_checked : acceptsGraphIso
    (source (graph core4480) (root 10) 2 2) DegreeTwoThreeSpectrum6167.graph sourceMap4480=true := by decide +kernel
theorem fusedMap4480_checked : acceptsGraphIso
    (fused (graph core4480) (root 10) 2 2) DegreeTwoThreeSpectrum5222.graph fusedMap4480=true := by decide +kernel
theorem certified4480 : Certified (graph core4480) (root 10) 2 2 :=
  of_native_maps core4480 DegreeTwoThreeSpectrum6167.graph DegreeTwoThreeSpectrum5222.graph
    sourceMap4480 fusedMap4480 sourceMap4480_checked fusedMap4480_checked
    DegreeTwoThreeFiniteComparisons.comparison4480
#print axioms sourceMap4480_checked
#print axioms fusedMap4480_checked
#print axioms certified4480
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
