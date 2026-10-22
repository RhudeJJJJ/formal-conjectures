/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4507 : Family 10 := level10.get ⟨313,by decide⟩
def sourceMap4507 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4507 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4507_checked : acceptsGraphIso
    (source (graph core4507) (root 10) 2 2) DegreeTwoThreeSpectrum6651.graph sourceMap4507=true := by decide +kernel
theorem fusedMap4507_checked : acceptsGraphIso
    (fused (graph core4507) (root 10) 2 2) DegreeTwoThreeSpectrum5516.graph fusedMap4507=true := by decide +kernel
theorem certified4507 : Certified (graph core4507) (root 10) 2 2 :=
  of_native_maps core4507 DegreeTwoThreeSpectrum6651.graph DegreeTwoThreeSpectrum5516.graph
    sourceMap4507 fusedMap4507 sourceMap4507_checked fusedMap4507_checked
    DegreeTwoThreeFiniteComparisons.comparison4507
#print axioms sourceMap4507_checked
#print axioms fusedMap4507_checked
#print axioms certified4507
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
