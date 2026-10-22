/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4539 : Family 10 := level10.get ⟨419,by decide⟩
def sourceMap4539 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,9,10,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4539 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4539_checked : acceptsGraphIso
    (source (graph core4539) (root 10) 2 2) DegreeTwoThreeSpectrum6822.graph sourceMap4539=true := by decide +kernel
theorem fusedMap4539_checked : acceptsGraphIso
    (fused (graph core4539) (root 10) 2 2) DegreeTwoThreeSpectrum5804.graph fusedMap4539=true := by decide +kernel
theorem certified4539 : Certified (graph core4539) (root 10) 2 2 :=
  of_native_maps core4539 DegreeTwoThreeSpectrum6822.graph DegreeTwoThreeSpectrum5804.graph
    sourceMap4539 fusedMap4539 sourceMap4539_checked fusedMap4539_checked
    DegreeTwoThreeFiniteComparisons.comparison4539
#print axioms sourceMap4539_checked
#print axioms fusedMap4539_checked
#print axioms certified4539
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
