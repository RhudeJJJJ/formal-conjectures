/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4799 : Family 10 := level10.get ⟨1131,by decide⟩
def sourceMap4799 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4799 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4799_checked : acceptsGraphIso
    (source (graph core4799) (root 10) 2 2) DegreeTwoThreeSpectrum7212.graph sourceMap4799=true := by decide +kernel
theorem fusedMap4799_checked : acceptsGraphIso
    (fused (graph core4799) (root 10) 2 2) DegreeTwoThreeSpectrum6249.graph fusedMap4799=true := by decide +kernel
theorem certified4799 : Certified (graph core4799) (root 10) 2 2 :=
  of_native_maps core4799 DegreeTwoThreeSpectrum7212.graph DegreeTwoThreeSpectrum6249.graph
    sourceMap4799 fusedMap4799 sourceMap4799_checked fusedMap4799_checked
    DegreeTwoThreeFiniteComparisons.comparison4799
#print axioms sourceMap4799_checked
#print axioms fusedMap4799_checked
#print axioms certified4799
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
