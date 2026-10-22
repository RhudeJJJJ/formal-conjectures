/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4476 : Family 10 := level10.get ⟨200,by decide⟩
def sourceMap4476 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4476 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4476_checked : acceptsGraphIso
    (source (graph core4476) (root 10) 2 2) DegreeTwoThreeSpectrum6112.graph sourceMap4476=true := by decide +kernel
theorem fusedMap4476_checked : acceptsGraphIso
    (fused (graph core4476) (root 10) 2 2) DegreeTwoThreeSpectrum5182.graph fusedMap4476=true := by decide +kernel
theorem certified4476 : Certified (graph core4476) (root 10) 2 2 :=
  of_native_maps core4476 DegreeTwoThreeSpectrum6112.graph DegreeTwoThreeSpectrum5182.graph
    sourceMap4476 fusedMap4476 sourceMap4476_checked fusedMap4476_checked
    DegreeTwoThreeFiniteComparisons.comparison4476
#print axioms sourceMap4476_checked
#print axioms fusedMap4476_checked
#print axioms certified4476
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
