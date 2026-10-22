/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4788 : Family 10 := level10.get ⟨1101,by decide⟩
def sourceMap4788 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4788 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4788_checked : acceptsGraphIso
    (source (graph core4788) (root 10) 2 2) DegreeTwoThreeSpectrum7181.graph sourceMap4788=true := by decide +kernel
theorem fusedMap4788_checked : acceptsGraphIso
    (fused (graph core4788) (root 10) 2 2) DegreeTwoThreeSpectrum6187.graph fusedMap4788=true := by decide +kernel
theorem certified4788 : Certified (graph core4788) (root 10) 2 2 :=
  of_native_maps core4788 DegreeTwoThreeSpectrum7181.graph DegreeTwoThreeSpectrum6187.graph
    sourceMap4788 fusedMap4788 sourceMap4788_checked fusedMap4788_checked
    DegreeTwoThreeFiniteComparisons.comparison4788
#print axioms sourceMap4788_checked
#print axioms fusedMap4788_checked
#print axioms certified4788
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
