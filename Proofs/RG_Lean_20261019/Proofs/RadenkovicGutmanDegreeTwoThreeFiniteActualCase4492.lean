/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4492 : Family 10 := level10.get ⟨263,by decide⟩
def sourceMap4492 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4492 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4492_checked : acceptsGraphIso
    (source (graph core4492) (root 10) 2 2) DegreeTwoThreeSpectrum6444.graph sourceMap4492=true := by decide +kernel
theorem fusedMap4492_checked : acceptsGraphIso
    (fused (graph core4492) (root 10) 2 2) DegreeTwoThreeSpectrum5378.graph fusedMap4492=true := by decide +kernel
theorem certified4492 : Certified (graph core4492) (root 10) 2 2 :=
  of_native_maps core4492 DegreeTwoThreeSpectrum6444.graph DegreeTwoThreeSpectrum5378.graph
    sourceMap4492 fusedMap4492 sourceMap4492_checked fusedMap4492_checked
    DegreeTwoThreeFiniteComparisons.comparison4492
#print axioms sourceMap4492_checked
#print axioms fusedMap4492_checked
#print axioms certified4492
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
