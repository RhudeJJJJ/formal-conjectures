/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4800 : Family 10 := level10.get ⟨1132,by decide⟩
def sourceMap4800 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4800 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4800_checked : acceptsGraphIso
    (source (graph core4800) (root 10) 2 2) DegreeTwoThreeSpectrum7213.graph sourceMap4800=true := by decide +kernel
theorem fusedMap4800_checked : acceptsGraphIso
    (fused (graph core4800) (root 10) 2 2) DegreeTwoThreeSpectrum6251.graph fusedMap4800=true := by decide +kernel
theorem certified4800 : Certified (graph core4800) (root 10) 2 2 :=
  of_native_maps core4800 DegreeTwoThreeSpectrum7213.graph DegreeTwoThreeSpectrum6251.graph
    sourceMap4800 fusedMap4800 sourceMap4800_checked fusedMap4800_checked
    DegreeTwoThreeFiniteComparisons.comparison4800
#print axioms sourceMap4800_checked
#print axioms fusedMap4800_checked
#print axioms certified4800
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
