/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4536 : Family 10 := level10.get ⟨410,by decide⟩
def sourceMap4536 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4536 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4536_checked : acceptsGraphIso
    (source (graph core4536) (root 10) 2 2) DegreeTwoThreeSpectrum6846.graph sourceMap4536=true := by decide +kernel
theorem fusedMap4536_checked : acceptsGraphIso
    (fused (graph core4536) (root 10) 2 2) DegreeTwoThreeSpectrum5782.graph fusedMap4536=true := by decide +kernel
theorem certified4536 : Certified (graph core4536) (root 10) 2 2 :=
  of_native_maps core4536 DegreeTwoThreeSpectrum6846.graph DegreeTwoThreeSpectrum5782.graph
    sourceMap4536 fusedMap4536 sourceMap4536_checked fusedMap4536_checked
    DegreeTwoThreeFiniteComparisons.comparison4536
#print axioms sourceMap4536_checked
#print axioms fusedMap4536_checked
#print axioms certified4536
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
